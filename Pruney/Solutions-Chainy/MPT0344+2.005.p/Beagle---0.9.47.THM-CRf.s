%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:19 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 144 expanded)
%              Number of leaves         :   23 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 342 expanded)
%              Number of equality atoms :   18 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_37,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_68,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_30,plain,(
    ! [B_13,A_12] :
      ( m1_subset_1(B_13,A_12)
      | ~ v1_xboole_0(B_13)
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_99,plain,(
    ! [B_39,A_40] :
      ( r2_hidden(B_39,A_40)
      | ~ m1_subset_1(B_39,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38,plain,(
    ! [C_20] :
      ( ~ r2_hidden(C_20,'#skF_5')
      | ~ m1_subset_1(C_20,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_115,plain,(
    ! [B_39] :
      ( ~ m1_subset_1(B_39,'#skF_4')
      | ~ m1_subset_1(B_39,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_99,c_38])).

tff(c_168,plain,(
    ! [B_49] :
      ( ~ m1_subset_1(B_49,'#skF_4')
      | ~ m1_subset_1(B_49,'#skF_5') ) ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_173,plain,(
    ! [B_13] :
      ( ~ m1_subset_1(B_13,'#skF_4')
      | ~ v1_xboole_0(B_13)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_168])).

tff(c_174,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_49,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_1'(A_26),A_26)
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_49,c_38])).

tff(c_56,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_53])).

tff(c_4,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,(
    ! [B_35,A_36] :
      ( m1_subset_1(B_35,A_36)
      | ~ r2_hidden(B_35,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_93,plain,(
    ! [A_2] :
      ( m1_subset_1('#skF_1'(A_2),A_2)
      | v1_xboole_0(A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(resolution,[status(thm)],[c_4,c_83])).

tff(c_58,plain,(
    ! [B_29,A_30] :
      ( m1_subset_1(B_29,A_30)
      | ~ v1_xboole_0(B_29)
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_62,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_56])).

tff(c_63,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    ! [B_13,A_12] :
      ( r2_hidden(B_13,A_12)
      | ~ m1_subset_1(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_158,plain,(
    ! [C_46,A_47,B_48] :
      ( r2_hidden(C_46,A_47)
      | ~ r2_hidden(C_46,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_931,plain,(
    ! [B_110,A_111,A_112] :
      ( r2_hidden(B_110,A_111)
      | ~ m1_subset_1(A_112,k1_zfmisc_1(A_111))
      | ~ m1_subset_1(B_110,A_112)
      | v1_xboole_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_28,c_158])).

tff(c_943,plain,(
    ! [B_110] :
      ( r2_hidden(B_110,'#skF_4')
      | ~ m1_subset_1(B_110,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_931])).

tff(c_976,plain,(
    ! [B_114] :
      ( r2_hidden(B_114,'#skF_4')
      | ~ m1_subset_1(B_114,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_943])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( m1_subset_1(B_13,A_12)
      | ~ r2_hidden(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_984,plain,(
    ! [B_114] :
      ( m1_subset_1(B_114,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_114,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_976,c_26])).

tff(c_990,plain,(
    ! [B_115] :
      ( m1_subset_1(B_115,'#skF_4')
      | ~ m1_subset_1(B_115,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_984])).

tff(c_994,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_93,c_990])).

tff(c_1002,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_174,c_56,c_994])).

tff(c_1004,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1007,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1004,c_2])).

tff(c_1011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1007])).

tff(c_1013,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1017,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1013,c_2])).

tff(c_1021,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1017,c_40])).

tff(c_34,plain,(
    ! [A_14] : ~ v1_xboole_0(k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1098,plain,(
    ! [B_130,A_131] :
      ( r2_hidden(B_130,A_131)
      | ~ m1_subset_1(B_130,A_131)
      | v1_xboole_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [C_11,A_7] :
      ( r1_tarski(C_11,A_7)
      | ~ r2_hidden(C_11,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1105,plain,(
    ! [B_130,A_7] :
      ( r1_tarski(B_130,A_7)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_1098,c_14])).

tff(c_1115,plain,(
    ! [B_132,A_133] :
      ( r1_tarski(B_132,A_133)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_133)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1105])).

tff(c_1128,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_1115])).

tff(c_12,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1020,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1017,c_12])).

tff(c_1075,plain,(
    ! [B_127,A_128] :
      ( B_127 = A_128
      | ~ r1_tarski(B_127,A_128)
      | ~ r1_tarski(A_128,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1080,plain,(
    ! [A_6] :
      ( A_6 = '#skF_4'
      | ~ r1_tarski(A_6,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1020,c_1075])).

tff(c_1141,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1128,c_1080])).

tff(c_1147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1021,c_1141])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:51:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.52  
% 2.99/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.52  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.99/1.52  
% 2.99/1.52  %Foreground sorts:
% 2.99/1.52  
% 2.99/1.52  
% 2.99/1.52  %Background operators:
% 2.99/1.52  
% 2.99/1.52  
% 2.99/1.52  %Foreground operators:
% 2.99/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.99/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.99/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.52  tff('#skF_5', type, '#skF_5': $i).
% 2.99/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.52  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.99/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.99/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.52  
% 3.15/1.53  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 3.15/1.53  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.15/1.53  tff(f_37, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.15/1.53  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.15/1.53  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.15/1.53  tff(f_68, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.15/1.53  tff(f_52, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.15/1.53  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.15/1.53  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.15/1.53  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.53  tff(c_30, plain, (![B_13, A_12]: (m1_subset_1(B_13, A_12) | ~v1_xboole_0(B_13) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.53  tff(c_99, plain, (![B_39, A_40]: (r2_hidden(B_39, A_40) | ~m1_subset_1(B_39, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.53  tff(c_38, plain, (![C_20]: (~r2_hidden(C_20, '#skF_5') | ~m1_subset_1(C_20, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.53  tff(c_115, plain, (![B_39]: (~m1_subset_1(B_39, '#skF_4') | ~m1_subset_1(B_39, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_99, c_38])).
% 3.15/1.53  tff(c_168, plain, (![B_49]: (~m1_subset_1(B_49, '#skF_4') | ~m1_subset_1(B_49, '#skF_5'))), inference(splitLeft, [status(thm)], [c_115])).
% 3.15/1.53  tff(c_173, plain, (![B_13]: (~m1_subset_1(B_13, '#skF_4') | ~v1_xboole_0(B_13) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_168])).
% 3.15/1.53  tff(c_174, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_173])).
% 3.15/1.53  tff(c_49, plain, (![A_26]: (r2_hidden('#skF_1'(A_26), A_26) | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.53  tff(c_53, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_4') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_49, c_38])).
% 3.15/1.53  tff(c_56, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_53])).
% 3.15/1.53  tff(c_4, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.53  tff(c_83, plain, (![B_35, A_36]: (m1_subset_1(B_35, A_36) | ~r2_hidden(B_35, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.53  tff(c_93, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), A_2) | v1_xboole_0(A_2) | k1_xboole_0=A_2)), inference(resolution, [status(thm)], [c_4, c_83])).
% 3.15/1.53  tff(c_58, plain, (![B_29, A_30]: (m1_subset_1(B_29, A_30) | ~v1_xboole_0(B_29) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.53  tff(c_62, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_56])).
% 3.15/1.53  tff(c_63, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_62])).
% 3.15/1.53  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.53  tff(c_28, plain, (![B_13, A_12]: (r2_hidden(B_13, A_12) | ~m1_subset_1(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.53  tff(c_158, plain, (![C_46, A_47, B_48]: (r2_hidden(C_46, A_47) | ~r2_hidden(C_46, B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.15/1.53  tff(c_931, plain, (![B_110, A_111, A_112]: (r2_hidden(B_110, A_111) | ~m1_subset_1(A_112, k1_zfmisc_1(A_111)) | ~m1_subset_1(B_110, A_112) | v1_xboole_0(A_112))), inference(resolution, [status(thm)], [c_28, c_158])).
% 3.15/1.53  tff(c_943, plain, (![B_110]: (r2_hidden(B_110, '#skF_4') | ~m1_subset_1(B_110, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_931])).
% 3.15/1.53  tff(c_976, plain, (![B_114]: (r2_hidden(B_114, '#skF_4') | ~m1_subset_1(B_114, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_174, c_943])).
% 3.15/1.53  tff(c_26, plain, (![B_13, A_12]: (m1_subset_1(B_13, A_12) | ~r2_hidden(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.53  tff(c_984, plain, (![B_114]: (m1_subset_1(B_114, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_114, '#skF_5'))), inference(resolution, [status(thm)], [c_976, c_26])).
% 3.15/1.53  tff(c_990, plain, (![B_115]: (m1_subset_1(B_115, '#skF_4') | ~m1_subset_1(B_115, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_63, c_984])).
% 3.15/1.53  tff(c_994, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_93, c_990])).
% 3.15/1.53  tff(c_1002, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_174, c_56, c_994])).
% 3.15/1.53  tff(c_1004, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_173])).
% 3.15/1.53  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.15/1.53  tff(c_1007, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1004, c_2])).
% 3.15/1.53  tff(c_1011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1007])).
% 3.15/1.53  tff(c_1013, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_62])).
% 3.15/1.53  tff(c_1017, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1013, c_2])).
% 3.15/1.53  tff(c_1021, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1017, c_40])).
% 3.15/1.53  tff(c_34, plain, (![A_14]: (~v1_xboole_0(k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.15/1.53  tff(c_1098, plain, (![B_130, A_131]: (r2_hidden(B_130, A_131) | ~m1_subset_1(B_130, A_131) | v1_xboole_0(A_131))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.53  tff(c_14, plain, (![C_11, A_7]: (r1_tarski(C_11, A_7) | ~r2_hidden(C_11, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.15/1.53  tff(c_1105, plain, (![B_130, A_7]: (r1_tarski(B_130, A_7) | ~m1_subset_1(B_130, k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_1098, c_14])).
% 3.15/1.53  tff(c_1115, plain, (![B_132, A_133]: (r1_tarski(B_132, A_133) | ~m1_subset_1(B_132, k1_zfmisc_1(A_133)))), inference(negUnitSimplification, [status(thm)], [c_34, c_1105])).
% 3.15/1.53  tff(c_1128, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_1115])).
% 3.15/1.53  tff(c_12, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.15/1.53  tff(c_1020, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1017, c_12])).
% 3.15/1.53  tff(c_1075, plain, (![B_127, A_128]: (B_127=A_128 | ~r1_tarski(B_127, A_128) | ~r1_tarski(A_128, B_127))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.15/1.53  tff(c_1080, plain, (![A_6]: (A_6='#skF_4' | ~r1_tarski(A_6, '#skF_4'))), inference(resolution, [status(thm)], [c_1020, c_1075])).
% 3.15/1.53  tff(c_1141, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_1128, c_1080])).
% 3.15/1.53  tff(c_1147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1021, c_1141])).
% 3.15/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.53  
% 3.15/1.53  Inference rules
% 3.15/1.53  ----------------------
% 3.15/1.53  #Ref     : 0
% 3.15/1.53  #Sup     : 223
% 3.15/1.53  #Fact    : 0
% 3.15/1.53  #Define  : 0
% 3.15/1.53  #Split   : 9
% 3.15/1.53  #Chain   : 0
% 3.15/1.53  #Close   : 0
% 3.15/1.53  
% 3.15/1.53  Ordering : KBO
% 3.15/1.53  
% 3.15/1.53  Simplification rules
% 3.15/1.53  ----------------------
% 3.15/1.53  #Subsume      : 50
% 3.15/1.53  #Demod        : 43
% 3.15/1.53  #Tautology    : 52
% 3.15/1.53  #SimpNegUnit  : 39
% 3.15/1.53  #BackRed      : 4
% 3.15/1.53  
% 3.15/1.53  #Partial instantiations: 0
% 3.15/1.53  #Strategies tried      : 1
% 3.15/1.53  
% 3.15/1.53  Timing (in seconds)
% 3.15/1.53  ----------------------
% 3.15/1.54  Preprocessing        : 0.33
% 3.15/1.54  Parsing              : 0.17
% 3.15/1.54  CNF conversion       : 0.03
% 3.15/1.54  Main loop            : 0.40
% 3.15/1.54  Inferencing          : 0.15
% 3.15/1.54  Reduction            : 0.11
% 3.15/1.54  Demodulation         : 0.07
% 3.15/1.54  BG Simplification    : 0.02
% 3.15/1.54  Subsumption          : 0.09
% 3.15/1.54  Abstraction          : 0.02
% 3.15/1.54  MUC search           : 0.00
% 3.15/1.54  Cooper               : 0.00
% 3.15/1.54  Total                : 0.77
% 3.15/1.54  Index Insertion      : 0.00
% 3.15/1.54  Index Deletion       : 0.00
% 3.15/1.54  Index Matching       : 0.00
% 3.15/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
