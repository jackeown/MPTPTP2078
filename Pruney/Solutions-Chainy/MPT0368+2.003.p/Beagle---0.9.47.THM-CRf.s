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
% DateTime   : Thu Dec  3 09:56:48 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 166 expanded)
%              Number of leaves         :   21 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 382 expanded)
%              Number of equality atoms :   10 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_780,plain,(
    ! [B_132,A_133] :
      ( m1_subset_1(B_132,A_133)
      | ~ v1_xboole_0(B_132)
      | ~ v1_xboole_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_51,plain,(
    ! [C_25] :
      ( r2_hidden(C_25,'#skF_6')
      | ~ m1_subset_1(C_25,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [C_25] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_25,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_51,c_2])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_69,plain,(
    ! [B_33,A_34] :
      ( v1_xboole_0(B_33)
      | ~ m1_subset_1(B_33,A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_72,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_69])).

tff(c_75,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_72])).

tff(c_42,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_xboole_0(A_5,B_6)
      | B_6 = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109,plain,(
    ! [B_45,A_46] :
      ( m1_subset_1(B_45,A_46)
      | ~ r2_hidden(B_45,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_124,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_109])).

tff(c_44,plain,(
    ! [C_20] :
      ( r2_hidden(C_20,'#skF_6')
      | ~ m1_subset_1(C_20,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_121,plain,(
    ! [C_20] :
      ( m1_subset_1(C_20,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_20,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_109])).

tff(c_133,plain,(
    ! [C_48] :
      ( m1_subset_1(C_48,'#skF_6')
      | ~ m1_subset_1(C_48,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_121])).

tff(c_142,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_124,c_133])).

tff(c_144,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_152,plain,(
    ! [B_50,A_51] :
      ( r2_hidden(B_50,A_51)
      | ~ m1_subset_1(B_50,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ! [C_16,A_12] :
      ( r1_tarski(C_16,A_12)
      | ~ r2_hidden(C_16,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_439,plain,(
    ! [B_84,A_85] :
      ( r1_tarski(B_84,A_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85))
      | v1_xboole_0(k1_zfmisc_1(A_85)) ) ),
    inference(resolution,[status(thm)],[c_152,c_22])).

tff(c_463,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_439])).

tff(c_475,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_463])).

tff(c_187,plain,(
    ! [A_54,B_55] :
      ( r2_xboole_0(A_54,B_55)
      | B_55 = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_91,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_2'(A_39,B_40),B_40)
      | ~ r2_xboole_0(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_100,plain,(
    ! [B_40,A_39] :
      ( ~ v1_xboole_0(B_40)
      | ~ r2_xboole_0(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_91,c_2])).

tff(c_198,plain,(
    ! [B_55,A_54] :
      ( ~ v1_xboole_0(B_55)
      | B_55 = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_187,c_100])).

tff(c_478,plain,
    ( ~ v1_xboole_0('#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_475,c_198])).

tff(c_483,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_478])).

tff(c_485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_483])).

tff(c_487,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),B_8)
      | ~ r2_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_660,plain,(
    ! [A_113,B_114] :
      ( m1_subset_1('#skF_2'(A_113,B_114),B_114)
      | v1_xboole_0(B_114)
      | ~ r2_xboole_0(A_113,B_114) ) ),
    inference(resolution,[status(thm)],[c_14,c_109])).

tff(c_506,plain,(
    ! [A_88,B_89] :
      ( ~ r2_hidden('#skF_2'(A_88,B_89),A_88)
      | ~ r2_xboole_0(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_526,plain,(
    ! [B_89] :
      ( ~ r2_xboole_0('#skF_6',B_89)
      | ~ m1_subset_1('#skF_2'('#skF_6',B_89),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_506])).

tff(c_668,plain,
    ( v1_xboole_0('#skF_5')
    | ~ r2_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_660,c_526])).

tff(c_679,plain,(
    ~ r2_xboole_0('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_487,c_668])).

tff(c_686,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_679])).

tff(c_689,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_686])).

tff(c_492,plain,(
    ! [B_86,A_87] :
      ( r2_hidden(B_86,A_87)
      | ~ m1_subset_1(B_86,A_87)
      | v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_717,plain,(
    ! [B_118,A_119] :
      ( r1_tarski(B_118,A_119)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_119))
      | v1_xboole_0(k1_zfmisc_1(A_119)) ) ),
    inference(resolution,[status(thm)],[c_492,c_22])).

tff(c_738,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_717])).

tff(c_748,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_689,c_738])).

tff(c_749,plain,(
    ! [C_25] : ~ m1_subset_1(C_25,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_789,plain,(
    ! [B_132] :
      ( ~ v1_xboole_0(B_132)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_780,c_749])).

tff(c_790,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_789])).

tff(c_817,plain,(
    ! [B_140,A_141] :
      ( m1_subset_1(B_140,A_141)
      | ~ r2_hidden(B_140,A_141)
      | v1_xboole_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_826,plain,(
    ! [A_142] :
      ( m1_subset_1('#skF_1'(A_142),A_142)
      | v1_xboole_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_4,c_817])).

tff(c_833,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_826,c_749])).

tff(c_838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_790,c_833])).

tff(c_839,plain,(
    ! [B_132] : ~ v1_xboole_0(B_132) ),
    inference(splitRight,[status(thm)],[c_789])).

tff(c_750,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_839,c_750])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:46:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.41  
% 2.59/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.41  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.59/1.41  
% 2.59/1.41  %Foreground sorts:
% 2.59/1.41  
% 2.59/1.41  
% 2.59/1.41  %Background operators:
% 2.59/1.41  
% 2.59/1.41  
% 2.59/1.41  %Foreground operators:
% 2.59/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.59/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.59/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.59/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.41  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.59/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.59/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.59/1.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.59/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.41  
% 2.59/1.43  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.59/1.43  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 2.59/1.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.59/1.43  tff(f_38, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.59/1.43  tff(f_61, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.59/1.43  tff(f_48, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.59/1.43  tff(c_780, plain, (![B_132, A_133]: (m1_subset_1(B_132, A_133) | ~v1_xboole_0(B_132) | ~v1_xboole_0(A_133))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.59/1.43  tff(c_51, plain, (![C_25]: (r2_hidden(C_25, '#skF_6') | ~m1_subset_1(C_25, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.59/1.43  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.43  tff(c_55, plain, (![C_25]: (~v1_xboole_0('#skF_6') | ~m1_subset_1(C_25, '#skF_5'))), inference(resolution, [status(thm)], [c_51, c_2])).
% 2.59/1.43  tff(c_56, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_55])).
% 2.59/1.43  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.59/1.43  tff(c_69, plain, (![B_33, A_34]: (v1_xboole_0(B_33) | ~m1_subset_1(B_33, A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.59/1.43  tff(c_72, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_69])).
% 2.59/1.43  tff(c_75, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_56, c_72])).
% 2.59/1.43  tff(c_42, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.59/1.43  tff(c_6, plain, (![A_5, B_6]: (r2_xboole_0(A_5, B_6) | B_6=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.59/1.43  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.43  tff(c_109, plain, (![B_45, A_46]: (m1_subset_1(B_45, A_46) | ~r2_hidden(B_45, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.59/1.43  tff(c_124, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_109])).
% 2.59/1.43  tff(c_44, plain, (![C_20]: (r2_hidden(C_20, '#skF_6') | ~m1_subset_1(C_20, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.59/1.43  tff(c_121, plain, (![C_20]: (m1_subset_1(C_20, '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(C_20, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_109])).
% 2.59/1.43  tff(c_133, plain, (![C_48]: (m1_subset_1(C_48, '#skF_6') | ~m1_subset_1(C_48, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_56, c_121])).
% 2.59/1.43  tff(c_142, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_124, c_133])).
% 2.59/1.43  tff(c_144, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_142])).
% 2.59/1.43  tff(c_152, plain, (![B_50, A_51]: (r2_hidden(B_50, A_51) | ~m1_subset_1(B_50, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.59/1.43  tff(c_22, plain, (![C_16, A_12]: (r1_tarski(C_16, A_12) | ~r2_hidden(C_16, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.59/1.43  tff(c_439, plain, (![B_84, A_85]: (r1_tarski(B_84, A_85) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)) | v1_xboole_0(k1_zfmisc_1(A_85)))), inference(resolution, [status(thm)], [c_152, c_22])).
% 2.59/1.43  tff(c_463, plain, (r1_tarski('#skF_6', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_439])).
% 2.59/1.43  tff(c_475, plain, (r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_75, c_463])).
% 2.59/1.43  tff(c_187, plain, (![A_54, B_55]: (r2_xboole_0(A_54, B_55) | B_55=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.59/1.43  tff(c_91, plain, (![A_39, B_40]: (r2_hidden('#skF_2'(A_39, B_40), B_40) | ~r2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.59/1.43  tff(c_100, plain, (![B_40, A_39]: (~v1_xboole_0(B_40) | ~r2_xboole_0(A_39, B_40))), inference(resolution, [status(thm)], [c_91, c_2])).
% 2.59/1.43  tff(c_198, plain, (![B_55, A_54]: (~v1_xboole_0(B_55) | B_55=A_54 | ~r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_187, c_100])).
% 2.59/1.43  tff(c_478, plain, (~v1_xboole_0('#skF_5') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_475, c_198])).
% 2.59/1.43  tff(c_483, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_478])).
% 2.59/1.43  tff(c_485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_483])).
% 2.59/1.43  tff(c_487, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_142])).
% 2.59/1.43  tff(c_14, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), B_8) | ~r2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.59/1.43  tff(c_660, plain, (![A_113, B_114]: (m1_subset_1('#skF_2'(A_113, B_114), B_114) | v1_xboole_0(B_114) | ~r2_xboole_0(A_113, B_114))), inference(resolution, [status(thm)], [c_14, c_109])).
% 2.59/1.43  tff(c_506, plain, (![A_88, B_89]: (~r2_hidden('#skF_2'(A_88, B_89), A_88) | ~r2_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.59/1.43  tff(c_526, plain, (![B_89]: (~r2_xboole_0('#skF_6', B_89) | ~m1_subset_1('#skF_2'('#skF_6', B_89), '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_506])).
% 2.59/1.43  tff(c_668, plain, (v1_xboole_0('#skF_5') | ~r2_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_660, c_526])).
% 2.59/1.43  tff(c_679, plain, (~r2_xboole_0('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_487, c_668])).
% 2.59/1.43  tff(c_686, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_679])).
% 2.59/1.43  tff(c_689, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_686])).
% 2.59/1.43  tff(c_492, plain, (![B_86, A_87]: (r2_hidden(B_86, A_87) | ~m1_subset_1(B_86, A_87) | v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.59/1.43  tff(c_717, plain, (![B_118, A_119]: (r1_tarski(B_118, A_119) | ~m1_subset_1(B_118, k1_zfmisc_1(A_119)) | v1_xboole_0(k1_zfmisc_1(A_119)))), inference(resolution, [status(thm)], [c_492, c_22])).
% 2.59/1.43  tff(c_738, plain, (r1_tarski('#skF_6', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_717])).
% 2.59/1.43  tff(c_748, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_689, c_738])).
% 2.59/1.43  tff(c_749, plain, (![C_25]: (~m1_subset_1(C_25, '#skF_5'))), inference(splitRight, [status(thm)], [c_55])).
% 2.59/1.43  tff(c_789, plain, (![B_132]: (~v1_xboole_0(B_132) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_780, c_749])).
% 2.59/1.43  tff(c_790, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_789])).
% 2.59/1.43  tff(c_817, plain, (![B_140, A_141]: (m1_subset_1(B_140, A_141) | ~r2_hidden(B_140, A_141) | v1_xboole_0(A_141))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.59/1.43  tff(c_826, plain, (![A_142]: (m1_subset_1('#skF_1'(A_142), A_142) | v1_xboole_0(A_142))), inference(resolution, [status(thm)], [c_4, c_817])).
% 2.59/1.43  tff(c_833, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_826, c_749])).
% 2.59/1.43  tff(c_838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_790, c_833])).
% 2.59/1.43  tff(c_839, plain, (![B_132]: (~v1_xboole_0(B_132))), inference(splitRight, [status(thm)], [c_789])).
% 2.59/1.43  tff(c_750, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_55])).
% 2.59/1.43  tff(c_844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_839, c_750])).
% 2.59/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.43  
% 2.59/1.43  Inference rules
% 2.59/1.43  ----------------------
% 2.59/1.43  #Ref     : 0
% 2.59/1.43  #Sup     : 155
% 2.59/1.43  #Fact    : 0
% 2.59/1.43  #Define  : 0
% 2.59/1.43  #Split   : 3
% 2.59/1.43  #Chain   : 0
% 2.59/1.43  #Close   : 0
% 2.59/1.43  
% 2.59/1.43  Ordering : KBO
% 2.59/1.43  
% 2.59/1.43  Simplification rules
% 2.59/1.43  ----------------------
% 2.59/1.43  #Subsume      : 38
% 2.59/1.43  #Demod        : 26
% 2.59/1.43  #Tautology    : 54
% 2.59/1.43  #SimpNegUnit  : 19
% 2.59/1.43  #BackRed      : 2
% 2.59/1.43  
% 2.59/1.43  #Partial instantiations: 0
% 2.59/1.43  #Strategies tried      : 1
% 2.59/1.43  
% 2.59/1.43  Timing (in seconds)
% 2.59/1.43  ----------------------
% 2.59/1.43  Preprocessing        : 0.29
% 2.59/1.43  Parsing              : 0.15
% 2.59/1.43  CNF conversion       : 0.02
% 2.59/1.43  Main loop            : 0.35
% 2.59/1.43  Inferencing          : 0.14
% 2.59/1.43  Reduction            : 0.09
% 2.59/1.43  Demodulation         : 0.06
% 2.59/1.43  BG Simplification    : 0.02
% 2.59/1.43  Subsumption          : 0.08
% 2.59/1.43  Abstraction          : 0.02
% 2.59/1.43  MUC search           : 0.00
% 2.59/1.43  Cooper               : 0.00
% 2.59/1.43  Total                : 0.68
% 2.59/1.43  Index Insertion      : 0.00
% 2.59/1.43  Index Deletion       : 0.00
% 2.59/1.43  Index Matching       : 0.00
% 2.59/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
