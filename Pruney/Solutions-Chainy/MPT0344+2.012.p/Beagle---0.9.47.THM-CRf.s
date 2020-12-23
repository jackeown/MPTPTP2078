%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:20 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 203 expanded)
%              Number of leaves         :   22 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  136 ( 489 expanded)
%              Number of equality atoms :   19 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_55,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( m1_subset_1(B_19,A_18)
      | ~ v1_xboole_0(B_19)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_109,plain,(
    ! [B_39,A_40] :
      ( r2_hidden(B_39,A_40)
      | ~ m1_subset_1(B_39,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    ! [C_21] :
      ( ~ r2_hidden(C_21,'#skF_7')
      | ~ m1_subset_1(C_21,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_122,plain,(
    ! [B_39] :
      ( ~ m1_subset_1(B_39,'#skF_6')
      | ~ m1_subset_1(B_39,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_109,c_36])).

tff(c_189,plain,(
    ! [B_52] :
      ( ~ m1_subset_1(B_52,'#skF_6')
      | ~ m1_subset_1(B_52,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_199,plain,(
    ! [B_19] :
      ( ~ m1_subset_1(B_19,'#skF_6')
      | ~ v1_xboole_0(B_19)
      | ~ v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_189])).

tff(c_200,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_54,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_3'(A_27),A_27)
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_58,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_7'),'#skF_6')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_54,c_36])).

tff(c_64,plain,(
    ~ m1_subset_1('#skF_3'('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_58])).

tff(c_12,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_156,plain,(
    ! [B_47,A_48] :
      ( m1_subset_1(B_47,A_48)
      | ~ r2_hidden(B_47,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_175,plain,(
    ! [A_10] :
      ( m1_subset_1('#skF_3'(A_10),A_10)
      | v1_xboole_0(A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(resolution,[status(thm)],[c_12,c_156])).

tff(c_74,plain,(
    ! [B_31,A_32] :
      ( m1_subset_1(B_31,A_32)
      | ~ v1_xboole_0(B_31)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_86,plain,
    ( ~ v1_xboole_0('#skF_3'('#skF_7'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_64])).

tff(c_98,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_68,plain,(
    ! [B_29,A_30] :
      ( v1_xboole_0(B_29)
      | ~ m1_subset_1(B_29,A_30)
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_72,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_68])).

tff(c_73,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_16,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_726,plain,(
    ! [B_112,A_113] :
      ( r1_tarski(B_112,A_113)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_113))
      | v1_xboole_0(k1_zfmisc_1(A_113)) ) ),
    inference(resolution,[status(thm)],[c_109,c_16])).

tff(c_744,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_726])).

tff(c_752,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_744])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( r2_hidden(B_19,A_18)
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_213,plain,(
    ! [C_55,B_56,A_57] :
      ( r2_hidden(C_55,B_56)
      | ~ r2_hidden(C_55,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_837,plain,(
    ! [B_127,B_128,A_129] :
      ( r2_hidden(B_127,B_128)
      | ~ r1_tarski(A_129,B_128)
      | ~ m1_subset_1(B_127,A_129)
      | v1_xboole_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_30,c_213])).

tff(c_843,plain,(
    ! [B_127] :
      ( r2_hidden(B_127,'#skF_6')
      | ~ m1_subset_1(B_127,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_752,c_837])).

tff(c_871,plain,(
    ! [B_130] :
      ( r2_hidden(B_130,'#skF_6')
      | ~ m1_subset_1(B_130,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_843])).

tff(c_28,plain,(
    ! [B_19,A_18] :
      ( m1_subset_1(B_19,A_18)
      | ~ r2_hidden(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_879,plain,(
    ! [B_130] :
      ( m1_subset_1(B_130,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(B_130,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_871,c_28])).

tff(c_894,plain,(
    ! [B_131] :
      ( m1_subset_1(B_131,'#skF_6')
      | ~ m1_subset_1(B_131,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_879])).

tff(c_902,plain,
    ( m1_subset_1('#skF_3'('#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_175,c_894])).

tff(c_917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_200,c_64,c_902])).

tff(c_919,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0(A_27)
      | k1_xboole_0 = A_27 ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_922,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_919,c_65])).

tff(c_926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_922])).

tff(c_928,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_932,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_928,c_65])).

tff(c_936,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_38])).

tff(c_1026,plain,(
    ! [B_149,A_150] :
      ( r2_hidden(B_149,A_150)
      | ~ m1_subset_1(B_149,A_150)
      | v1_xboole_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1558,plain,(
    ! [B_200,A_201] :
      ( r1_tarski(B_200,A_201)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(A_201))
      | v1_xboole_0(k1_zfmisc_1(A_201)) ) ),
    inference(resolution,[status(thm)],[c_1026,c_16])).

tff(c_1579,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_1558])).

tff(c_1590,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_1579])).

tff(c_934,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | A_10 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_12])).

tff(c_1085,plain,(
    ! [C_157,B_158,A_159] :
      ( r2_hidden(C_157,B_158)
      | ~ r2_hidden(C_157,A_159)
      | ~ r1_tarski(A_159,B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1174,plain,(
    ! [A_168,B_169] :
      ( r2_hidden('#skF_3'(A_168),B_169)
      | ~ r1_tarski(A_168,B_169)
      | A_168 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_934,c_1085])).

tff(c_1195,plain,(
    ! [B_169,A_168] :
      ( ~ v1_xboole_0(B_169)
      | ~ r1_tarski(A_168,B_169)
      | A_168 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_1174,c_2])).

tff(c_1600,plain,
    ( ~ v1_xboole_0('#skF_6')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1590,c_1195])).

tff(c_1606,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_1600])).

tff(c_1608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_936,c_1606])).

tff(c_1609,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1613,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1609,c_65])).

tff(c_1617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1613])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 16:08:53 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.61  
% 3.35/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.61  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 3.66/1.61  
% 3.66/1.61  %Foreground sorts:
% 3.66/1.61  
% 3.66/1.61  
% 3.66/1.61  %Background operators:
% 3.66/1.61  
% 3.66/1.61  
% 3.66/1.61  %Foreground operators:
% 3.66/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.66/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.66/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.66/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.66/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.66/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.61  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.66/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.66/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.66/1.61  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.66/1.61  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.66/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.61  
% 3.66/1.63  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 3.66/1.63  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.66/1.63  tff(f_46, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.66/1.63  tff(f_55, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.66/1.63  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.66/1.63  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.66/1.63  tff(c_38, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.66/1.63  tff(c_32, plain, (![B_19, A_18]: (m1_subset_1(B_19, A_18) | ~v1_xboole_0(B_19) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.66/1.63  tff(c_109, plain, (![B_39, A_40]: (r2_hidden(B_39, A_40) | ~m1_subset_1(B_39, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.66/1.63  tff(c_36, plain, (![C_21]: (~r2_hidden(C_21, '#skF_7') | ~m1_subset_1(C_21, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.66/1.63  tff(c_122, plain, (![B_39]: (~m1_subset_1(B_39, '#skF_6') | ~m1_subset_1(B_39, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_109, c_36])).
% 3.66/1.63  tff(c_189, plain, (![B_52]: (~m1_subset_1(B_52, '#skF_6') | ~m1_subset_1(B_52, '#skF_7'))), inference(splitLeft, [status(thm)], [c_122])).
% 3.66/1.63  tff(c_199, plain, (![B_19]: (~m1_subset_1(B_19, '#skF_6') | ~v1_xboole_0(B_19) | ~v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_32, c_189])).
% 3.66/1.63  tff(c_200, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_199])).
% 3.66/1.63  tff(c_54, plain, (![A_27]: (r2_hidden('#skF_3'(A_27), A_27) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.66/1.63  tff(c_58, plain, (~m1_subset_1('#skF_3'('#skF_7'), '#skF_6') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_54, c_36])).
% 3.66/1.63  tff(c_64, plain, (~m1_subset_1('#skF_3'('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_38, c_58])).
% 3.66/1.63  tff(c_12, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.66/1.63  tff(c_156, plain, (![B_47, A_48]: (m1_subset_1(B_47, A_48) | ~r2_hidden(B_47, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.66/1.63  tff(c_175, plain, (![A_10]: (m1_subset_1('#skF_3'(A_10), A_10) | v1_xboole_0(A_10) | k1_xboole_0=A_10)), inference(resolution, [status(thm)], [c_12, c_156])).
% 3.66/1.63  tff(c_74, plain, (![B_31, A_32]: (m1_subset_1(B_31, A_32) | ~v1_xboole_0(B_31) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.66/1.63  tff(c_86, plain, (~v1_xboole_0('#skF_3'('#skF_7')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_74, c_64])).
% 3.66/1.63  tff(c_98, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_86])).
% 3.66/1.63  tff(c_40, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.66/1.63  tff(c_68, plain, (![B_29, A_30]: (v1_xboole_0(B_29) | ~m1_subset_1(B_29, A_30) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.66/1.63  tff(c_72, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_68])).
% 3.66/1.63  tff(c_73, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_72])).
% 3.66/1.63  tff(c_16, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.66/1.63  tff(c_726, plain, (![B_112, A_113]: (r1_tarski(B_112, A_113) | ~m1_subset_1(B_112, k1_zfmisc_1(A_113)) | v1_xboole_0(k1_zfmisc_1(A_113)))), inference(resolution, [status(thm)], [c_109, c_16])).
% 3.66/1.63  tff(c_744, plain, (r1_tarski('#skF_7', '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_726])).
% 3.66/1.63  tff(c_752, plain, (r1_tarski('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_73, c_744])).
% 3.66/1.63  tff(c_30, plain, (![B_19, A_18]: (r2_hidden(B_19, A_18) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.66/1.63  tff(c_213, plain, (![C_55, B_56, A_57]: (r2_hidden(C_55, B_56) | ~r2_hidden(C_55, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.66/1.63  tff(c_837, plain, (![B_127, B_128, A_129]: (r2_hidden(B_127, B_128) | ~r1_tarski(A_129, B_128) | ~m1_subset_1(B_127, A_129) | v1_xboole_0(A_129))), inference(resolution, [status(thm)], [c_30, c_213])).
% 3.66/1.63  tff(c_843, plain, (![B_127]: (r2_hidden(B_127, '#skF_6') | ~m1_subset_1(B_127, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_752, c_837])).
% 3.66/1.63  tff(c_871, plain, (![B_130]: (r2_hidden(B_130, '#skF_6') | ~m1_subset_1(B_130, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_200, c_843])).
% 3.66/1.63  tff(c_28, plain, (![B_19, A_18]: (m1_subset_1(B_19, A_18) | ~r2_hidden(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.66/1.63  tff(c_879, plain, (![B_130]: (m1_subset_1(B_130, '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(B_130, '#skF_7'))), inference(resolution, [status(thm)], [c_871, c_28])).
% 3.66/1.63  tff(c_894, plain, (![B_131]: (m1_subset_1(B_131, '#skF_6') | ~m1_subset_1(B_131, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_98, c_879])).
% 3.66/1.63  tff(c_902, plain, (m1_subset_1('#skF_3'('#skF_7'), '#skF_6') | v1_xboole_0('#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_175, c_894])).
% 3.66/1.63  tff(c_917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_200, c_64, c_902])).
% 3.66/1.63  tff(c_919, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_199])).
% 3.66/1.63  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.66/1.63  tff(c_65, plain, (![A_27]: (~v1_xboole_0(A_27) | k1_xboole_0=A_27)), inference(resolution, [status(thm)], [c_54, c_2])).
% 3.66/1.63  tff(c_922, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_919, c_65])).
% 3.66/1.63  tff(c_926, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_922])).
% 3.66/1.63  tff(c_928, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_86])).
% 3.66/1.63  tff(c_932, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_928, c_65])).
% 3.66/1.63  tff(c_936, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_932, c_38])).
% 3.66/1.63  tff(c_1026, plain, (![B_149, A_150]: (r2_hidden(B_149, A_150) | ~m1_subset_1(B_149, A_150) | v1_xboole_0(A_150))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.66/1.63  tff(c_1558, plain, (![B_200, A_201]: (r1_tarski(B_200, A_201) | ~m1_subset_1(B_200, k1_zfmisc_1(A_201)) | v1_xboole_0(k1_zfmisc_1(A_201)))), inference(resolution, [status(thm)], [c_1026, c_16])).
% 3.66/1.63  tff(c_1579, plain, (r1_tarski('#skF_7', '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_1558])).
% 3.66/1.63  tff(c_1590, plain, (r1_tarski('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_73, c_1579])).
% 3.66/1.63  tff(c_934, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | A_10='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_932, c_12])).
% 3.66/1.63  tff(c_1085, plain, (![C_157, B_158, A_159]: (r2_hidden(C_157, B_158) | ~r2_hidden(C_157, A_159) | ~r1_tarski(A_159, B_158))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.66/1.63  tff(c_1174, plain, (![A_168, B_169]: (r2_hidden('#skF_3'(A_168), B_169) | ~r1_tarski(A_168, B_169) | A_168='#skF_6')), inference(resolution, [status(thm)], [c_934, c_1085])).
% 3.66/1.63  tff(c_1195, plain, (![B_169, A_168]: (~v1_xboole_0(B_169) | ~r1_tarski(A_168, B_169) | A_168='#skF_6')), inference(resolution, [status(thm)], [c_1174, c_2])).
% 3.66/1.63  tff(c_1600, plain, (~v1_xboole_0('#skF_6') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_1590, c_1195])).
% 3.66/1.63  tff(c_1606, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_928, c_1600])).
% 3.66/1.63  tff(c_1608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_936, c_1606])).
% 3.66/1.63  tff(c_1609, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_72])).
% 3.66/1.63  tff(c_1613, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1609, c_65])).
% 3.66/1.63  tff(c_1617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1613])).
% 3.66/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.63  
% 3.66/1.63  Inference rules
% 3.66/1.63  ----------------------
% 3.66/1.63  #Ref     : 0
% 3.66/1.63  #Sup     : 331
% 3.66/1.63  #Fact    : 0
% 3.66/1.63  #Define  : 0
% 3.66/1.63  #Split   : 9
% 3.66/1.63  #Chain   : 0
% 3.66/1.63  #Close   : 0
% 3.66/1.63  
% 3.66/1.63  Ordering : KBO
% 3.66/1.63  
% 3.66/1.63  Simplification rules
% 3.66/1.63  ----------------------
% 3.66/1.63  #Subsume      : 93
% 3.66/1.63  #Demod        : 51
% 3.66/1.63  #Tautology    : 70
% 3.66/1.63  #SimpNegUnit  : 40
% 3.66/1.63  #BackRed      : 12
% 3.66/1.63  
% 3.66/1.63  #Partial instantiations: 0
% 3.66/1.63  #Strategies tried      : 1
% 3.66/1.63  
% 3.66/1.63  Timing (in seconds)
% 3.66/1.63  ----------------------
% 3.66/1.63  Preprocessing        : 0.30
% 3.66/1.63  Parsing              : 0.15
% 3.66/1.63  CNF conversion       : 0.02
% 3.66/1.63  Main loop            : 0.55
% 3.66/1.63  Inferencing          : 0.22
% 3.66/1.63  Reduction            : 0.14
% 3.66/1.63  Demodulation         : 0.08
% 3.66/1.63  BG Simplification    : 0.03
% 3.66/1.63  Subsumption          : 0.12
% 3.66/1.63  Abstraction          : 0.02
% 3.66/1.63  MUC search           : 0.00
% 3.66/1.63  Cooper               : 0.00
% 3.66/1.63  Total                : 0.89
% 3.66/1.63  Index Insertion      : 0.00
% 3.66/1.63  Index Deletion       : 0.00
% 3.66/1.63  Index Matching       : 0.00
% 3.66/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
