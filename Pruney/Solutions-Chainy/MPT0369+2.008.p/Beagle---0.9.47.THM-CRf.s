%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:52 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   62 (  77 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :   84 ( 142 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_85,plain,(
    ! [B_35,A_36] :
      ( v1_xboole_0(B_35)
      | ~ m1_subset_1(B_35,A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_97,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_85])).

tff(c_98,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( r2_hidden(B_17,A_16)
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_42,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1127,plain,(
    ! [A_147,B_148] :
      ( k4_xboole_0(A_147,B_148) = k3_subset_1(A_147,B_148)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(A_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1136,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1127])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1120,plain,(
    ! [C_144,A_145,B_146] :
      ( r2_hidden(C_144,A_145)
      | ~ r2_hidden(C_144,B_146)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(A_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1320,plain,(
    ! [A_176,B_177,A_178] :
      ( r2_hidden('#skF_1'(A_176,B_177),A_178)
      | ~ m1_subset_1(A_176,k1_zfmisc_1(A_178))
      | r1_tarski(A_176,B_177) ) ),
    inference(resolution,[status(thm)],[c_8,c_1120])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1351,plain,(
    ! [A_179,A_180] :
      ( ~ m1_subset_1(A_179,k1_zfmisc_1(A_180))
      | r1_tarski(A_179,A_180) ) ),
    inference(resolution,[status(thm)],[c_1320,c_6])).

tff(c_1365,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_1351])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1373,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1365,c_26])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1003,plain,(
    ! [A_129,B_130] : k5_xboole_0(A_129,k3_xboole_0(A_129,B_130)) = k4_xboole_0(A_129,B_130) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1012,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1003])).

tff(c_1377,plain,(
    k5_xboole_0('#skF_2','#skF_3') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1373,c_1012])).

tff(c_1383,plain,(
    k5_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1136,c_1377])).

tff(c_22,plain,(
    ! [A_9,C_11,B_10] :
      ( r2_hidden(A_9,C_11)
      | ~ r2_hidden(A_9,B_10)
      | r2_hidden(A_9,k5_xboole_0(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1483,plain,(
    ! [A_190] :
      ( r2_hidden(A_190,'#skF_3')
      | ~ r2_hidden(A_190,'#skF_2')
      | r2_hidden(A_190,k3_subset_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1383,c_22])).

tff(c_40,plain,(
    ~ r2_hidden('#skF_4',k3_subset_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1503,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_1483,c_40])).

tff(c_1512,plain,(
    ~ r2_hidden('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1503])).

tff(c_1515,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1512])).

tff(c_1518,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1515])).

tff(c_1520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_1518])).

tff(c_1522,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_10,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1530,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1522,c_10])).

tff(c_1534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1530])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:50:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.53  
% 3.25/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.53  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.25/1.53  
% 3.25/1.53  %Foreground sorts:
% 3.25/1.53  
% 3.25/1.53  
% 3.25/1.53  %Background operators:
% 3.25/1.53  
% 3.25/1.53  
% 3.25/1.53  %Foreground operators:
% 3.25/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.25/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.25/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.53  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.25/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.25/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.25/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.25/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.53  
% 3.25/1.54  tff(f_90, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 3.25/1.54  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.25/1.54  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.25/1.54  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.25/1.54  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.25/1.54  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.25/1.54  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.25/1.54  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.25/1.54  tff(f_45, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.25/1.54  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.25/1.54  tff(c_48, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.25/1.54  tff(c_44, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.25/1.54  tff(c_85, plain, (![B_35, A_36]: (v1_xboole_0(B_35) | ~m1_subset_1(B_35, A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.25/1.54  tff(c_97, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_85])).
% 3.25/1.54  tff(c_98, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_97])).
% 3.25/1.54  tff(c_30, plain, (![B_17, A_16]: (r2_hidden(B_17, A_16) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.25/1.54  tff(c_42, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.25/1.54  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.25/1.54  tff(c_1127, plain, (![A_147, B_148]: (k4_xboole_0(A_147, B_148)=k3_subset_1(A_147, B_148) | ~m1_subset_1(B_148, k1_zfmisc_1(A_147)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.25/1.54  tff(c_1136, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_1127])).
% 3.25/1.54  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.25/1.54  tff(c_1120, plain, (![C_144, A_145, B_146]: (r2_hidden(C_144, A_145) | ~r2_hidden(C_144, B_146) | ~m1_subset_1(B_146, k1_zfmisc_1(A_145)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.25/1.54  tff(c_1320, plain, (![A_176, B_177, A_178]: (r2_hidden('#skF_1'(A_176, B_177), A_178) | ~m1_subset_1(A_176, k1_zfmisc_1(A_178)) | r1_tarski(A_176, B_177))), inference(resolution, [status(thm)], [c_8, c_1120])).
% 3.25/1.54  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.25/1.54  tff(c_1351, plain, (![A_179, A_180]: (~m1_subset_1(A_179, k1_zfmisc_1(A_180)) | r1_tarski(A_179, A_180))), inference(resolution, [status(thm)], [c_1320, c_6])).
% 3.25/1.54  tff(c_1365, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_1351])).
% 3.25/1.54  tff(c_26, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.25/1.54  tff(c_1373, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_1365, c_26])).
% 3.25/1.54  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.25/1.54  tff(c_1003, plain, (![A_129, B_130]: (k5_xboole_0(A_129, k3_xboole_0(A_129, B_130))=k4_xboole_0(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.25/1.54  tff(c_1012, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1003])).
% 3.25/1.54  tff(c_1377, plain, (k5_xboole_0('#skF_2', '#skF_3')=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1373, c_1012])).
% 3.25/1.54  tff(c_1383, plain, (k5_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1136, c_1377])).
% 3.25/1.54  tff(c_22, plain, (![A_9, C_11, B_10]: (r2_hidden(A_9, C_11) | ~r2_hidden(A_9, B_10) | r2_hidden(A_9, k5_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.25/1.54  tff(c_1483, plain, (![A_190]: (r2_hidden(A_190, '#skF_3') | ~r2_hidden(A_190, '#skF_2') | r2_hidden(A_190, k3_subset_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1383, c_22])).
% 3.25/1.54  tff(c_40, plain, (~r2_hidden('#skF_4', k3_subset_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.25/1.54  tff(c_1503, plain, (r2_hidden('#skF_4', '#skF_3') | ~r2_hidden('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_1483, c_40])).
% 3.25/1.54  tff(c_1512, plain, (~r2_hidden('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_1503])).
% 3.25/1.54  tff(c_1515, plain, (~m1_subset_1('#skF_4', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1512])).
% 3.25/1.54  tff(c_1518, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1515])).
% 3.25/1.54  tff(c_1520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_1518])).
% 3.25/1.54  tff(c_1522, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_97])).
% 3.25/1.54  tff(c_10, plain, (![A_8]: (k1_xboole_0=A_8 | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.25/1.54  tff(c_1530, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1522, c_10])).
% 3.25/1.54  tff(c_1534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1530])).
% 3.25/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.54  
% 3.25/1.54  Inference rules
% 3.25/1.54  ----------------------
% 3.25/1.54  #Ref     : 0
% 3.25/1.54  #Sup     : 339
% 3.25/1.54  #Fact    : 0
% 3.25/1.54  #Define  : 0
% 3.25/1.54  #Split   : 10
% 3.25/1.54  #Chain   : 0
% 3.25/1.54  #Close   : 0
% 3.25/1.54  
% 3.25/1.54  Ordering : KBO
% 3.25/1.54  
% 3.25/1.54  Simplification rules
% 3.25/1.54  ----------------------
% 3.25/1.54  #Subsume      : 28
% 3.25/1.54  #Demod        : 42
% 3.25/1.54  #Tautology    : 113
% 3.25/1.54  #SimpNegUnit  : 20
% 3.25/1.54  #BackRed      : 2
% 3.25/1.54  
% 3.25/1.54  #Partial instantiations: 0
% 3.25/1.54  #Strategies tried      : 1
% 3.25/1.54  
% 3.25/1.54  Timing (in seconds)
% 3.25/1.54  ----------------------
% 3.52/1.55  Preprocessing        : 0.28
% 3.52/1.55  Parsing              : 0.15
% 3.52/1.55  CNF conversion       : 0.02
% 3.52/1.55  Main loop            : 0.48
% 3.52/1.55  Inferencing          : 0.18
% 3.52/1.55  Reduction            : 0.14
% 3.52/1.55  Demodulation         : 0.10
% 3.52/1.55  BG Simplification    : 0.02
% 3.52/1.55  Subsumption          : 0.10
% 3.52/1.55  Abstraction          : 0.02
% 3.52/1.55  MUC search           : 0.00
% 3.52/1.55  Cooper               : 0.00
% 3.52/1.55  Total                : 0.79
% 3.52/1.55  Index Insertion      : 0.00
% 3.52/1.55  Index Deletion       : 0.00
% 3.52/1.55  Index Matching       : 0.00
% 3.52/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
