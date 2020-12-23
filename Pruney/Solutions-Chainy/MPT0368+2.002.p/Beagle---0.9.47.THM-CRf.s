%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:48 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 169 expanded)
%              Number of leaves         :   20 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 390 expanded)
%              Number of equality atoms :    6 (  23 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_74,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_1325,plain,(
    ! [B_177,A_178] :
      ( m1_subset_1(B_177,A_178)
      | ~ v1_xboole_0(B_177)
      | ~ v1_xboole_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_51,plain,(
    ! [C_25] :
      ( r2_hidden(C_25,'#skF_6')
      | ~ m1_subset_1(C_25,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

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

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_74,plain,(
    ! [B_34,A_35] :
      ( v1_xboole_0(B_34)
      | ~ m1_subset_1(B_34,A_35)
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_80,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_74])).

tff(c_84,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_80])).

tff(c_38,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [B_36,A_37] :
      ( m1_subset_1(B_36,A_37)
      | ~ r2_hidden(B_36,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_99,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_85])).

tff(c_40,plain,(
    ! [C_20] :
      ( r2_hidden(C_20,'#skF_6')
      | ~ m1_subset_1(C_20,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_91,plain,(
    ! [C_20] :
      ( m1_subset_1(C_20,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_20,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_85])).

tff(c_116,plain,(
    ! [C_41] :
      ( m1_subset_1(C_41,'#skF_6')
      | ~ m1_subset_1(C_41,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_91])).

tff(c_125,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_99,c_116])).

tff(c_127,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_171,plain,(
    ! [B_50,A_51] :
      ( r2_hidden(B_50,A_51)
      | ~ m1_subset_1(B_50,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [C_16,A_12] :
      ( r1_tarski(C_16,A_12)
      | ~ r2_hidden(C_16,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_833,plain,(
    ! [B_119,A_120] :
      ( r1_tarski(B_119,A_120)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_120))
      | v1_xboole_0(k1_zfmisc_1(A_120)) ) ),
    inference(resolution,[status(thm)],[c_171,c_18])).

tff(c_860,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_833])).

tff(c_873,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_860])).

tff(c_221,plain,(
    ! [C_59,B_60,A_61] :
      ( r2_hidden(C_59,B_60)
      | ~ r2_hidden(C_59,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_302,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_1'(A_68),B_69)
      | ~ r1_tarski(A_68,B_69)
      | v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_4,c_221])).

tff(c_318,plain,(
    ! [B_69,A_68] :
      ( ~ v1_xboole_0(B_69)
      | ~ r1_tarski(A_68,B_69)
      | v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_302,c_2])).

tff(c_878,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_873,c_318])).

tff(c_891,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_878])).

tff(c_893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_891])).

tff(c_895,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_919,plain,(
    ! [A_123,B_124] :
      ( r2_hidden('#skF_2'(A_123,B_124),A_123)
      | r1_tarski(A_123,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    ! [B_18,A_17] :
      ( m1_subset_1(B_18,A_17)
      | ~ r2_hidden(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1181,plain,(
    ! [A_160,B_161] :
      ( m1_subset_1('#skF_2'(A_160,B_161),A_160)
      | v1_xboole_0(A_160)
      | r1_tarski(A_160,B_161) ) ),
    inference(resolution,[status(thm)],[c_919,c_30])).

tff(c_100,plain,(
    ! [A_38,B_39] :
      ( ~ r2_hidden('#skF_2'(A_38,B_39),B_39)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_110,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_38,'#skF_6'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_100])).

tff(c_1185,plain,
    ( v1_xboole_0('#skF_5')
    | r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1181,c_110])).

tff(c_1195,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_895,c_1185])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1207,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_1195,c_12])).

tff(c_1214,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1207])).

tff(c_900,plain,(
    ! [B_121,A_122] :
      ( r2_hidden(B_121,A_122)
      | ~ m1_subset_1(B_121,A_122)
      | v1_xboole_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1278,plain,(
    ! [B_168,A_169] :
      ( r1_tarski(B_168,A_169)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(A_169))
      | v1_xboole_0(k1_zfmisc_1(A_169)) ) ),
    inference(resolution,[status(thm)],[c_900,c_18])).

tff(c_1296,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_1278])).

tff(c_1305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1214,c_1296])).

tff(c_1306,plain,(
    ! [C_25] : ~ m1_subset_1(C_25,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_1330,plain,(
    ! [B_177] :
      ( ~ v1_xboole_0(B_177)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1325,c_1306])).

tff(c_1331,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1330])).

tff(c_1370,plain,(
    ! [B_187,A_188] :
      ( m1_subset_1(B_187,A_188)
      | ~ r2_hidden(B_187,A_188)
      | v1_xboole_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1383,plain,(
    ! [A_189] :
      ( m1_subset_1('#skF_1'(A_189),A_189)
      | v1_xboole_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_4,c_1370])).

tff(c_1390,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1383,c_1306])).

tff(c_1395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1331,c_1390])).

tff(c_1396,plain,(
    ! [B_177] : ~ v1_xboole_0(B_177) ),
    inference(splitRight,[status(thm)],[c_1330])).

tff(c_1307,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_1411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1396,c_1307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.65  
% 3.34/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.65  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.34/1.65  
% 3.34/1.65  %Foreground sorts:
% 3.34/1.65  
% 3.34/1.65  
% 3.34/1.65  %Background operators:
% 3.34/1.65  
% 3.34/1.65  
% 3.34/1.65  %Foreground operators:
% 3.34/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.34/1.65  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.34/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.34/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.34/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.65  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.34/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.34/1.65  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.34/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.65  
% 3.34/1.67  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.34/1.67  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 3.34/1.67  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.34/1.67  tff(f_51, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.34/1.67  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.34/1.67  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.34/1.67  tff(c_1325, plain, (![B_177, A_178]: (m1_subset_1(B_177, A_178) | ~v1_xboole_0(B_177) | ~v1_xboole_0(A_178))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.34/1.67  tff(c_51, plain, (![C_25]: (r2_hidden(C_25, '#skF_6') | ~m1_subset_1(C_25, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.34/1.67  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.34/1.67  tff(c_55, plain, (![C_25]: (~v1_xboole_0('#skF_6') | ~m1_subset_1(C_25, '#skF_5'))), inference(resolution, [status(thm)], [c_51, c_2])).
% 3.34/1.67  tff(c_56, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_55])).
% 3.34/1.67  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.34/1.67  tff(c_74, plain, (![B_34, A_35]: (v1_xboole_0(B_34) | ~m1_subset_1(B_34, A_35) | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.34/1.67  tff(c_80, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_74])).
% 3.34/1.67  tff(c_84, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_56, c_80])).
% 3.34/1.67  tff(c_38, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.34/1.67  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.34/1.67  tff(c_85, plain, (![B_36, A_37]: (m1_subset_1(B_36, A_37) | ~r2_hidden(B_36, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.34/1.67  tff(c_99, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_85])).
% 3.34/1.67  tff(c_40, plain, (![C_20]: (r2_hidden(C_20, '#skF_6') | ~m1_subset_1(C_20, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.34/1.67  tff(c_91, plain, (![C_20]: (m1_subset_1(C_20, '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(C_20, '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_85])).
% 3.34/1.67  tff(c_116, plain, (![C_41]: (m1_subset_1(C_41, '#skF_6') | ~m1_subset_1(C_41, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_56, c_91])).
% 3.34/1.67  tff(c_125, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_99, c_116])).
% 3.34/1.67  tff(c_127, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_125])).
% 3.34/1.67  tff(c_171, plain, (![B_50, A_51]: (r2_hidden(B_50, A_51) | ~m1_subset_1(B_50, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.34/1.67  tff(c_18, plain, (![C_16, A_12]: (r1_tarski(C_16, A_12) | ~r2_hidden(C_16, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.34/1.67  tff(c_833, plain, (![B_119, A_120]: (r1_tarski(B_119, A_120) | ~m1_subset_1(B_119, k1_zfmisc_1(A_120)) | v1_xboole_0(k1_zfmisc_1(A_120)))), inference(resolution, [status(thm)], [c_171, c_18])).
% 3.34/1.67  tff(c_860, plain, (r1_tarski('#skF_6', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_833])).
% 3.34/1.67  tff(c_873, plain, (r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_84, c_860])).
% 3.34/1.67  tff(c_221, plain, (![C_59, B_60, A_61]: (r2_hidden(C_59, B_60) | ~r2_hidden(C_59, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.34/1.67  tff(c_302, plain, (![A_68, B_69]: (r2_hidden('#skF_1'(A_68), B_69) | ~r1_tarski(A_68, B_69) | v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_4, c_221])).
% 3.34/1.67  tff(c_318, plain, (![B_69, A_68]: (~v1_xboole_0(B_69) | ~r1_tarski(A_68, B_69) | v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_302, c_2])).
% 3.34/1.67  tff(c_878, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_873, c_318])).
% 3.34/1.67  tff(c_891, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_878])).
% 3.34/1.67  tff(c_893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_891])).
% 3.34/1.67  tff(c_895, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_125])).
% 3.34/1.67  tff(c_919, plain, (![A_123, B_124]: (r2_hidden('#skF_2'(A_123, B_124), A_123) | r1_tarski(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.34/1.67  tff(c_30, plain, (![B_18, A_17]: (m1_subset_1(B_18, A_17) | ~r2_hidden(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.34/1.67  tff(c_1181, plain, (![A_160, B_161]: (m1_subset_1('#skF_2'(A_160, B_161), A_160) | v1_xboole_0(A_160) | r1_tarski(A_160, B_161))), inference(resolution, [status(thm)], [c_919, c_30])).
% 3.34/1.67  tff(c_100, plain, (![A_38, B_39]: (~r2_hidden('#skF_2'(A_38, B_39), B_39) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.34/1.67  tff(c_110, plain, (![A_38]: (r1_tarski(A_38, '#skF_6') | ~m1_subset_1('#skF_2'(A_38, '#skF_6'), '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_100])).
% 3.34/1.67  tff(c_1185, plain, (v1_xboole_0('#skF_5') | r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1181, c_110])).
% 3.34/1.67  tff(c_1195, plain, (r1_tarski('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_895, c_1185])).
% 3.34/1.67  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.34/1.67  tff(c_1207, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_1195, c_12])).
% 3.34/1.67  tff(c_1214, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_1207])).
% 3.34/1.67  tff(c_900, plain, (![B_121, A_122]: (r2_hidden(B_121, A_122) | ~m1_subset_1(B_121, A_122) | v1_xboole_0(A_122))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.34/1.67  tff(c_1278, plain, (![B_168, A_169]: (r1_tarski(B_168, A_169) | ~m1_subset_1(B_168, k1_zfmisc_1(A_169)) | v1_xboole_0(k1_zfmisc_1(A_169)))), inference(resolution, [status(thm)], [c_900, c_18])).
% 3.34/1.67  tff(c_1296, plain, (r1_tarski('#skF_6', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_1278])).
% 3.34/1.67  tff(c_1305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_1214, c_1296])).
% 3.34/1.67  tff(c_1306, plain, (![C_25]: (~m1_subset_1(C_25, '#skF_5'))), inference(splitRight, [status(thm)], [c_55])).
% 3.34/1.67  tff(c_1330, plain, (![B_177]: (~v1_xboole_0(B_177) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_1325, c_1306])).
% 3.34/1.67  tff(c_1331, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1330])).
% 3.34/1.67  tff(c_1370, plain, (![B_187, A_188]: (m1_subset_1(B_187, A_188) | ~r2_hidden(B_187, A_188) | v1_xboole_0(A_188))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.34/1.67  tff(c_1383, plain, (![A_189]: (m1_subset_1('#skF_1'(A_189), A_189) | v1_xboole_0(A_189))), inference(resolution, [status(thm)], [c_4, c_1370])).
% 3.34/1.67  tff(c_1390, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1383, c_1306])).
% 3.34/1.67  tff(c_1395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1331, c_1390])).
% 3.34/1.67  tff(c_1396, plain, (![B_177]: (~v1_xboole_0(B_177))), inference(splitRight, [status(thm)], [c_1330])).
% 3.34/1.67  tff(c_1307, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_55])).
% 3.34/1.67  tff(c_1411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1396, c_1307])).
% 3.34/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.67  
% 3.34/1.67  Inference rules
% 3.34/1.67  ----------------------
% 3.34/1.67  #Ref     : 0
% 3.34/1.67  #Sup     : 291
% 3.34/1.67  #Fact    : 0
% 3.34/1.67  #Define  : 0
% 3.34/1.67  #Split   : 5
% 3.34/1.67  #Chain   : 0
% 3.34/1.67  #Close   : 0
% 3.34/1.67  
% 3.34/1.67  Ordering : KBO
% 3.34/1.67  
% 3.34/1.67  Simplification rules
% 3.34/1.67  ----------------------
% 3.34/1.67  #Subsume      : 94
% 3.34/1.67  #Demod        : 49
% 3.34/1.67  #Tautology    : 74
% 3.34/1.67  #SimpNegUnit  : 34
% 3.34/1.67  #BackRed      : 8
% 3.34/1.67  
% 3.34/1.67  #Partial instantiations: 0
% 3.34/1.67  #Strategies tried      : 1
% 3.34/1.67  
% 3.34/1.67  Timing (in seconds)
% 3.34/1.67  ----------------------
% 3.34/1.67  Preprocessing        : 0.37
% 3.34/1.67  Parsing              : 0.18
% 3.34/1.67  CNF conversion       : 0.03
% 3.34/1.67  Main loop            : 0.51
% 3.34/1.67  Inferencing          : 0.20
% 3.34/1.67  Reduction            : 0.13
% 3.34/1.67  Demodulation         : 0.08
% 3.34/1.67  BG Simplification    : 0.03
% 3.34/1.67  Subsumption          : 0.12
% 3.34/1.67  Abstraction          : 0.02
% 3.34/1.67  MUC search           : 0.00
% 3.34/1.67  Cooper               : 0.00
% 3.34/1.67  Total                : 0.91
% 3.34/1.67  Index Insertion      : 0.00
% 3.34/1.67  Index Deletion       : 0.00
% 3.34/1.67  Index Matching       : 0.00
% 3.34/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
