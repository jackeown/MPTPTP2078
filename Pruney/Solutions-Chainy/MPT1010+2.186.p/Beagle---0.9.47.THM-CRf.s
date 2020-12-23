%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:30 EST 2020

% Result     : Theorem 5.80s
% Output     : CNFRefutation 5.80s
% Verified   : 
% Statistics : Number of formulae       :   61 (  83 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :   80 ( 161 expanded)
%              Number of equality atoms :   19 (  38 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_42,plain,(
    k1_funct_1('#skF_7','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_48,plain,(
    v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_44,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3086,plain,(
    ! [D_5162,C_5163,B_5164,A_5165] :
      ( r2_hidden(k1_funct_1(D_5162,C_5163),B_5164)
      | k1_xboole_0 = B_5164
      | ~ r2_hidden(C_5163,A_5165)
      | ~ m1_subset_1(D_5162,k1_zfmisc_1(k2_zfmisc_1(A_5165,B_5164)))
      | ~ v1_funct_2(D_5162,A_5165,B_5164)
      | ~ v1_funct_1(D_5162) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6266,plain,(
    ! [D_7451,B_7452] :
      ( r2_hidden(k1_funct_1(D_7451,'#skF_6'),B_7452)
      | k1_xboole_0 = B_7452
      | ~ m1_subset_1(D_7451,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_7452)))
      | ~ v1_funct_2(D_7451,'#skF_4',B_7452)
      | ~ v1_funct_1(D_7451) ) ),
    inference(resolution,[status(thm)],[c_44,c_3086])).

tff(c_6279,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5'))
    | k1_tarski('#skF_5') = k1_xboole_0
    | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_6266])).

tff(c_6283,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5'))
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_6279])).

tff(c_6284,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6283])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_120,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden('#skF_1'(A_47,B_48),B_48)
      | r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_125,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_120])).

tff(c_52,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [D_11,B_7] : r2_hidden(D_11,k2_tarski(D_11,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_58,plain,(
    ! [A_28] : r2_hidden(A_28,k1_tarski(A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_14])).

tff(c_34,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_128,plain,(
    ! [C_52,B_53,A_54] :
      ( ~ v1_xboole_0(C_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(C_52))
      | ~ r2_hidden(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_135,plain,(
    ! [B_55,A_56,A_57] :
      ( ~ v1_xboole_0(B_55)
      | ~ r2_hidden(A_56,A_57)
      | ~ r1_tarski(A_57,B_55) ) ),
    inference(resolution,[status(thm)],[c_34,c_128])).

tff(c_190,plain,(
    ! [B_64,A_65] :
      ( ~ v1_xboole_0(B_64)
      | ~ r1_tarski(k1_tarski(A_65),B_64) ) ),
    inference(resolution,[status(thm)],[c_58,c_135])).

tff(c_195,plain,(
    ! [A_65] : ~ v1_xboole_0(k1_tarski(A_65)) ),
    inference(resolution,[status(thm)],[c_125,c_190])).

tff(c_6357,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6284,c_195])).

tff(c_6417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6357])).

tff(c_6418,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6283])).

tff(c_28,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_204,plain,(
    ! [D_69,B_70,A_71] :
      ( D_69 = B_70
      | D_69 = A_71
      | ~ r2_hidden(D_69,k2_tarski(A_71,B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_218,plain,(
    ! [D_69,A_12] :
      ( D_69 = A_12
      | D_69 = A_12
      | ~ r2_hidden(D_69,k1_tarski(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_204])).

tff(c_6431,plain,(
    k1_funct_1('#skF_7','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6418,c_218])).

tff(c_6484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_42,c_6431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:20:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.80/2.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.14  
% 5.80/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.15  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.80/2.15  
% 5.80/2.15  %Foreground sorts:
% 5.80/2.15  
% 5.80/2.15  
% 5.80/2.15  %Background operators:
% 5.80/2.15  
% 5.80/2.15  
% 5.80/2.15  %Foreground operators:
% 5.80/2.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.80/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.80/2.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.80/2.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.80/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.80/2.15  tff('#skF_7', type, '#skF_7': $i).
% 5.80/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.80/2.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.80/2.15  tff('#skF_5', type, '#skF_5': $i).
% 5.80/2.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.80/2.15  tff('#skF_6', type, '#skF_6': $i).
% 5.80/2.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.80/2.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.80/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.80/2.15  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.80/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.80/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.80/2.15  tff('#skF_4', type, '#skF_4': $i).
% 5.80/2.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.80/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.80/2.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.80/2.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.80/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.80/2.15  
% 5.80/2.16  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 5.80/2.16  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.80/2.16  tff(f_74, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 5.80/2.16  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.80/2.16  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.80/2.16  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 5.80/2.16  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.80/2.16  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.80/2.16  tff(c_42, plain, (k1_funct_1('#skF_7', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.80/2.16  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.80/2.16  tff(c_50, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.80/2.16  tff(c_48, plain, (v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.80/2.16  tff(c_46, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.80/2.16  tff(c_44, plain, (r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.80/2.16  tff(c_3086, plain, (![D_5162, C_5163, B_5164, A_5165]: (r2_hidden(k1_funct_1(D_5162, C_5163), B_5164) | k1_xboole_0=B_5164 | ~r2_hidden(C_5163, A_5165) | ~m1_subset_1(D_5162, k1_zfmisc_1(k2_zfmisc_1(A_5165, B_5164))) | ~v1_funct_2(D_5162, A_5165, B_5164) | ~v1_funct_1(D_5162))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.80/2.16  tff(c_6266, plain, (![D_7451, B_7452]: (r2_hidden(k1_funct_1(D_7451, '#skF_6'), B_7452) | k1_xboole_0=B_7452 | ~m1_subset_1(D_7451, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_7452))) | ~v1_funct_2(D_7451, '#skF_4', B_7452) | ~v1_funct_1(D_7451))), inference(resolution, [status(thm)], [c_44, c_3086])).
% 5.80/2.16  tff(c_6279, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5')) | k1_tarski('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_46, c_6266])).
% 5.80/2.16  tff(c_6283, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5')) | k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_6279])).
% 5.80/2.16  tff(c_6284, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6283])).
% 5.80/2.16  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.80/2.16  tff(c_120, plain, (![A_47, B_48]: (~r2_hidden('#skF_1'(A_47, B_48), B_48) | r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.80/2.16  tff(c_125, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_120])).
% 5.80/2.16  tff(c_52, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.80/2.16  tff(c_14, plain, (![D_11, B_7]: (r2_hidden(D_11, k2_tarski(D_11, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.80/2.16  tff(c_58, plain, (![A_28]: (r2_hidden(A_28, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_14])).
% 5.80/2.16  tff(c_34, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.80/2.16  tff(c_128, plain, (![C_52, B_53, A_54]: (~v1_xboole_0(C_52) | ~m1_subset_1(B_53, k1_zfmisc_1(C_52)) | ~r2_hidden(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.80/2.16  tff(c_135, plain, (![B_55, A_56, A_57]: (~v1_xboole_0(B_55) | ~r2_hidden(A_56, A_57) | ~r1_tarski(A_57, B_55))), inference(resolution, [status(thm)], [c_34, c_128])).
% 5.80/2.16  tff(c_190, plain, (![B_64, A_65]: (~v1_xboole_0(B_64) | ~r1_tarski(k1_tarski(A_65), B_64))), inference(resolution, [status(thm)], [c_58, c_135])).
% 5.80/2.16  tff(c_195, plain, (![A_65]: (~v1_xboole_0(k1_tarski(A_65)))), inference(resolution, [status(thm)], [c_125, c_190])).
% 5.80/2.16  tff(c_6357, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6284, c_195])).
% 5.80/2.16  tff(c_6417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_6357])).
% 5.80/2.16  tff(c_6418, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_6283])).
% 5.80/2.16  tff(c_28, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.80/2.16  tff(c_204, plain, (![D_69, B_70, A_71]: (D_69=B_70 | D_69=A_71 | ~r2_hidden(D_69, k2_tarski(A_71, B_70)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.80/2.16  tff(c_218, plain, (![D_69, A_12]: (D_69=A_12 | D_69=A_12 | ~r2_hidden(D_69, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_204])).
% 5.80/2.16  tff(c_6431, plain, (k1_funct_1('#skF_7', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_6418, c_218])).
% 5.80/2.16  tff(c_6484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_42, c_6431])).
% 5.80/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.16  
% 5.80/2.16  Inference rules
% 5.80/2.16  ----------------------
% 5.80/2.16  #Ref     : 0
% 5.80/2.16  #Sup     : 1043
% 5.80/2.16  #Fact    : 14
% 5.80/2.16  #Define  : 0
% 5.80/2.16  #Split   : 13
% 5.80/2.16  #Chain   : 0
% 5.80/2.16  #Close   : 0
% 5.80/2.16  
% 5.80/2.16  Ordering : KBO
% 5.80/2.16  
% 5.80/2.16  Simplification rules
% 5.80/2.16  ----------------------
% 5.80/2.16  #Subsume      : 315
% 5.80/2.16  #Demod        : 137
% 5.80/2.16  #Tautology    : 220
% 5.80/2.16  #SimpNegUnit  : 71
% 5.80/2.16  #BackRed      : 8
% 5.80/2.16  
% 5.80/2.16  #Partial instantiations: 5460
% 5.80/2.16  #Strategies tried      : 1
% 5.80/2.16  
% 5.80/2.16  Timing (in seconds)
% 5.80/2.16  ----------------------
% 5.80/2.16  Preprocessing        : 0.33
% 5.80/2.16  Parsing              : 0.17
% 5.80/2.16  CNF conversion       : 0.02
% 5.80/2.16  Main loop            : 1.06
% 5.80/2.16  Inferencing          : 0.50
% 5.80/2.16  Reduction            : 0.25
% 5.80/2.16  Demodulation         : 0.16
% 5.80/2.16  BG Simplification    : 0.04
% 5.80/2.16  Subsumption          : 0.19
% 5.80/2.16  Abstraction          : 0.05
% 5.80/2.16  MUC search           : 0.00
% 5.80/2.16  Cooper               : 0.00
% 5.80/2.16  Total                : 1.42
% 5.80/2.16  Index Insertion      : 0.00
% 5.80/2.16  Index Deletion       : 0.00
% 5.80/2.16  Index Matching       : 0.00
% 5.80/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
