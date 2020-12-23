%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:52 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 117 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 237 expanded)
%              Number of equality atoms :   18 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_70,plain,(
    m1_subset_1('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_125,plain,(
    ! [B_50,A_51] :
      ( v1_xboole_0(B_50)
      | ~ m1_subset_1(B_50,A_51)
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_133,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_125])).

tff(c_134,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_56,plain,(
    ! [B_28,A_27] :
      ( r2_hidden(B_28,A_27)
      | ~ m1_subset_1(B_28,A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_68,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_72,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_446,plain,(
    ! [A_94,B_95] :
      ( k4_xboole_0(A_94,B_95) = k3_subset_1(A_94,B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_466,plain,(
    k4_xboole_0('#skF_7','#skF_8') = k3_subset_1('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_446])).

tff(c_591,plain,(
    ! [D_104,A_105,B_106] :
      ( r2_hidden(D_104,k4_xboole_0(A_105,B_106))
      | r2_hidden(D_104,B_106)
      | ~ r2_hidden(D_104,A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_796,plain,(
    ! [D_117] :
      ( r2_hidden(D_117,k3_subset_1('#skF_7','#skF_8'))
      | r2_hidden(D_117,'#skF_8')
      | ~ r2_hidden(D_117,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_591])).

tff(c_66,plain,(
    ~ r2_hidden('#skF_9',k3_subset_1('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_819,plain,
    ( r2_hidden('#skF_9','#skF_8')
    | ~ r2_hidden('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_796,c_66])).

tff(c_831,plain,(
    ~ r2_hidden('#skF_9','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_819])).

tff(c_834,plain,
    ( ~ m1_subset_1('#skF_9','#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_831])).

tff(c_837,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_834])).

tff(c_839,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_837])).

tff(c_840,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_841,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_886,plain,(
    ! [A_129,B_130] :
      ( r2_hidden('#skF_2'(A_129,B_130),A_129)
      | r1_tarski(A_129,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_899,plain,(
    ! [A_129,B_130] :
      ( ~ v1_xboole_0(A_129)
      | r1_tarski(A_129,B_130) ) ),
    inference(resolution,[status(thm)],[c_886,c_2])).

tff(c_900,plain,(
    ! [A_131,B_132] :
      ( ~ v1_xboole_0(A_131)
      | r1_tarski(A_131,B_132) ) ),
    inference(resolution,[status(thm)],[c_886,c_2])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( B_17 = A_16
      | ~ r1_tarski(B_17,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_945,plain,(
    ! [B_137,A_138] :
      ( B_137 = A_138
      | ~ r1_tarski(B_137,A_138)
      | ~ v1_xboole_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_900,c_30])).

tff(c_1001,plain,(
    ! [B_141,A_142] :
      ( B_141 = A_142
      | ~ v1_xboole_0(B_141)
      | ~ v1_xboole_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_899,c_945])).

tff(c_1008,plain,(
    ! [A_143] :
      ( A_143 = '#skF_7'
      | ~ v1_xboole_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_841,c_1001])).

tff(c_1017,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_840,c_1008])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1026,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1017,c_74])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [B_17] : r1_tarski(B_17,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_84,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_88,plain,(
    ! [B_17] : k4_xboole_0(B_17,B_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_84])).

tff(c_1033,plain,(
    ! [D_144,B_145,A_146] :
      ( ~ r2_hidden(D_144,B_145)
      | ~ r2_hidden(D_144,k4_xboole_0(A_146,B_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1104,plain,(
    ! [D_150,B_151] :
      ( ~ r2_hidden(D_150,B_151)
      | ~ r2_hidden(D_150,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_1033])).

tff(c_1130,plain,(
    ! [A_154] :
      ( ~ r2_hidden('#skF_1'(A_154),k1_xboole_0)
      | v1_xboole_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_4,c_1104])).

tff(c_1139,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_1130])).

tff(c_1007,plain,(
    ! [A_142] :
      ( A_142 = '#skF_9'
      | ~ v1_xboole_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_840,c_1001])).

tff(c_1142,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1139,c_1007])).

tff(c_1150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1026,c_1142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:19:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.51  
% 3.28/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.51  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_5
% 3.28/1.51  
% 3.28/1.51  %Foreground sorts:
% 3.28/1.51  
% 3.28/1.51  
% 3.28/1.51  %Background operators:
% 3.28/1.51  
% 3.28/1.51  
% 3.28/1.51  %Foreground operators:
% 3.28/1.51  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.28/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.28/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.28/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.28/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.28/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.28/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.51  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.28/1.51  tff('#skF_9', type, '#skF_9': $i).
% 3.28/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.51  tff('#skF_8', type, '#skF_8': $i).
% 3.28/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.28/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.28/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.28/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.28/1.51  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.28/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.51  
% 3.28/1.53  tff(f_102, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 3.28/1.53  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.28/1.53  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.28/1.53  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.28/1.53  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.28/1.53  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.28/1.53  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.28/1.53  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.28/1.53  tff(c_70, plain, (m1_subset_1('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.28/1.53  tff(c_125, plain, (![B_50, A_51]: (v1_xboole_0(B_50) | ~m1_subset_1(B_50, A_51) | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.28/1.53  tff(c_133, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_70, c_125])).
% 3.28/1.53  tff(c_134, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_133])).
% 3.28/1.53  tff(c_56, plain, (![B_28, A_27]: (r2_hidden(B_28, A_27) | ~m1_subset_1(B_28, A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.28/1.53  tff(c_68, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.28/1.53  tff(c_72, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.28/1.53  tff(c_446, plain, (![A_94, B_95]: (k4_xboole_0(A_94, B_95)=k3_subset_1(A_94, B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.28/1.53  tff(c_466, plain, (k4_xboole_0('#skF_7', '#skF_8')=k3_subset_1('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_72, c_446])).
% 3.28/1.53  tff(c_591, plain, (![D_104, A_105, B_106]: (r2_hidden(D_104, k4_xboole_0(A_105, B_106)) | r2_hidden(D_104, B_106) | ~r2_hidden(D_104, A_105))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.28/1.53  tff(c_796, plain, (![D_117]: (r2_hidden(D_117, k3_subset_1('#skF_7', '#skF_8')) | r2_hidden(D_117, '#skF_8') | ~r2_hidden(D_117, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_466, c_591])).
% 3.28/1.53  tff(c_66, plain, (~r2_hidden('#skF_9', k3_subset_1('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.28/1.53  tff(c_819, plain, (r2_hidden('#skF_9', '#skF_8') | ~r2_hidden('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_796, c_66])).
% 3.28/1.53  tff(c_831, plain, (~r2_hidden('#skF_9', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_68, c_819])).
% 3.28/1.53  tff(c_834, plain, (~m1_subset_1('#skF_9', '#skF_7') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_56, c_831])).
% 3.28/1.53  tff(c_837, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_834])).
% 3.28/1.53  tff(c_839, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_837])).
% 3.28/1.53  tff(c_840, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_133])).
% 3.28/1.53  tff(c_841, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_133])).
% 3.28/1.53  tff(c_886, plain, (![A_129, B_130]: (r2_hidden('#skF_2'(A_129, B_130), A_129) | r1_tarski(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.28/1.53  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.53  tff(c_899, plain, (![A_129, B_130]: (~v1_xboole_0(A_129) | r1_tarski(A_129, B_130))), inference(resolution, [status(thm)], [c_886, c_2])).
% 3.28/1.53  tff(c_900, plain, (![A_131, B_132]: (~v1_xboole_0(A_131) | r1_tarski(A_131, B_132))), inference(resolution, [status(thm)], [c_886, c_2])).
% 3.28/1.53  tff(c_30, plain, (![B_17, A_16]: (B_17=A_16 | ~r1_tarski(B_17, A_16) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.28/1.53  tff(c_945, plain, (![B_137, A_138]: (B_137=A_138 | ~r1_tarski(B_137, A_138) | ~v1_xboole_0(A_138))), inference(resolution, [status(thm)], [c_900, c_30])).
% 3.28/1.53  tff(c_1001, plain, (![B_141, A_142]: (B_141=A_142 | ~v1_xboole_0(B_141) | ~v1_xboole_0(A_142))), inference(resolution, [status(thm)], [c_899, c_945])).
% 3.28/1.53  tff(c_1008, plain, (![A_143]: (A_143='#skF_7' | ~v1_xboole_0(A_143))), inference(resolution, [status(thm)], [c_841, c_1001])).
% 3.28/1.53  tff(c_1017, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_840, c_1008])).
% 3.28/1.53  tff(c_74, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.28/1.53  tff(c_1026, plain, (k1_xboole_0!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1017, c_74])).
% 3.28/1.53  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.53  tff(c_34, plain, (![B_17]: (r1_tarski(B_17, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.28/1.53  tff(c_84, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.28/1.53  tff(c_88, plain, (![B_17]: (k4_xboole_0(B_17, B_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_84])).
% 3.28/1.53  tff(c_1033, plain, (![D_144, B_145, A_146]: (~r2_hidden(D_144, B_145) | ~r2_hidden(D_144, k4_xboole_0(A_146, B_145)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.28/1.53  tff(c_1104, plain, (![D_150, B_151]: (~r2_hidden(D_150, B_151) | ~r2_hidden(D_150, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_88, c_1033])).
% 3.28/1.53  tff(c_1130, plain, (![A_154]: (~r2_hidden('#skF_1'(A_154), k1_xboole_0) | v1_xboole_0(A_154))), inference(resolution, [status(thm)], [c_4, c_1104])).
% 3.28/1.53  tff(c_1139, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1130])).
% 3.28/1.53  tff(c_1007, plain, (![A_142]: (A_142='#skF_9' | ~v1_xboole_0(A_142))), inference(resolution, [status(thm)], [c_840, c_1001])).
% 3.28/1.53  tff(c_1142, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_1139, c_1007])).
% 3.28/1.53  tff(c_1150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1026, c_1142])).
% 3.28/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.53  
% 3.28/1.53  Inference rules
% 3.28/1.53  ----------------------
% 3.28/1.53  #Ref     : 0
% 3.28/1.53  #Sup     : 238
% 3.28/1.53  #Fact    : 0
% 3.28/1.53  #Define  : 0
% 3.28/1.53  #Split   : 8
% 3.28/1.53  #Chain   : 0
% 3.28/1.53  #Close   : 0
% 3.28/1.53  
% 3.28/1.53  Ordering : KBO
% 3.28/1.53  
% 3.28/1.53  Simplification rules
% 3.28/1.53  ----------------------
% 3.28/1.53  #Subsume      : 33
% 3.28/1.53  #Demod        : 40
% 3.28/1.53  #Tautology    : 74
% 3.28/1.53  #SimpNegUnit  : 23
% 3.28/1.53  #BackRed      : 10
% 3.28/1.53  
% 3.28/1.53  #Partial instantiations: 0
% 3.28/1.53  #Strategies tried      : 1
% 3.28/1.53  
% 3.28/1.53  Timing (in seconds)
% 3.28/1.53  ----------------------
% 3.28/1.53  Preprocessing        : 0.33
% 3.28/1.53  Parsing              : 0.16
% 3.28/1.53  CNF conversion       : 0.03
% 3.28/1.53  Main loop            : 0.42
% 3.28/1.53  Inferencing          : 0.15
% 3.28/1.53  Reduction            : 0.12
% 3.28/1.53  Demodulation         : 0.08
% 3.28/1.53  BG Simplification    : 0.02
% 3.28/1.53  Subsumption          : 0.09
% 3.28/1.53  Abstraction          : 0.02
% 3.28/1.53  MUC search           : 0.00
% 3.28/1.53  Cooper               : 0.00
% 3.28/1.53  Total                : 0.78
% 3.28/1.53  Index Insertion      : 0.00
% 3.28/1.53  Index Deletion       : 0.00
% 3.28/1.53  Index Matching       : 0.00
% 3.28/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
