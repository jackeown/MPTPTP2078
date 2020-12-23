%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:16 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 140 expanded)
%              Number of leaves         :   22 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  105 ( 319 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                   => r2_hidden(D,C) ) )
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_50,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_36,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_143,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_168,plain,(
    ! [A_56,B_57] :
      ( ~ v1_xboole_0(A_56)
      | r1_tarski(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_143,c_8])).

tff(c_177,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_168,c_36])).

tff(c_28,plain,(
    ! [B_17,A_16] :
      ( m1_subset_1(B_17,A_16)
      | ~ r2_hidden(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_164,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1('#skF_1'(A_54,B_55),A_54)
      | v1_xboole_0(A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_143,c_28])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    ! [A_15] : r1_tarski(k1_tarski(A_15),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_58,plain,(
    ! [A_35,B_36] :
      ( r2_hidden(A_35,B_36)
      | ~ r1_tarski(k1_tarski(A_35),B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_63,plain,(
    ! [A_37] : r2_hidden(A_37,k1_zfmisc_1(A_37)) ),
    inference(resolution,[status(thm)],[c_26,c_58])).

tff(c_71,plain,(
    ! [A_37] : ~ v1_xboole_0(k1_zfmisc_1(A_37)) ),
    inference(resolution,[status(thm)],[c_63,c_8])).

tff(c_178,plain,(
    ! [B_58,A_59] :
      ( r2_hidden(B_58,A_59)
      | ~ m1_subset_1(B_58,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [C_12,A_8] :
      ( r1_tarski(C_12,A_8)
      | ~ r2_hidden(C_12,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_193,plain,(
    ! [B_58,A_8] :
      ( r1_tarski(B_58,A_8)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_8))
      | v1_xboole_0(k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_178,c_10])).

tff(c_204,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(B_60,A_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_193])).

tff(c_226,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_204])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_227,plain,(
    ! [C_62,B_63,A_64] :
      ( r2_hidden(C_62,B_63)
      | ~ r2_hidden(C_62,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_350,plain,(
    ! [A_85,B_86,B_87] :
      ( r2_hidden('#skF_1'(A_85,B_86),B_87)
      | ~ r1_tarski(A_85,B_87)
      | r1_tarski(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_6,c_227])).

tff(c_399,plain,(
    ! [B_90,A_91,B_92] :
      ( ~ v1_xboole_0(B_90)
      | ~ r1_tarski(A_91,B_90)
      | r1_tarski(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_350,c_8])).

tff(c_421,plain,(
    ! [B_92] :
      ( ~ v1_xboole_0('#skF_4')
      | r1_tarski('#skF_5',B_92) ) ),
    inference(resolution,[status(thm)],[c_226,c_399])).

tff(c_427,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_421])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( r2_hidden(B_17,A_16)
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_453,plain,(
    ! [B_94,B_95,A_96] :
      ( r2_hidden(B_94,B_95)
      | ~ r1_tarski(A_96,B_95)
      | ~ m1_subset_1(B_94,A_96)
      | v1_xboole_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_30,c_227])).

tff(c_461,plain,(
    ! [B_94] :
      ( r2_hidden(B_94,'#skF_4')
      | ~ m1_subset_1(B_94,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_226,c_453])).

tff(c_489,plain,(
    ! [B_97] :
      ( r2_hidden(B_97,'#skF_4')
      | ~ m1_subset_1(B_97,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_461])).

tff(c_498,plain,(
    ! [B_97] :
      ( m1_subset_1(B_97,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_97,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_489,c_28])).

tff(c_548,plain,(
    ! [B_101] :
      ( m1_subset_1(B_101,'#skF_4')
      | ~ m1_subset_1(B_101,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_498])).

tff(c_552,plain,(
    ! [B_55] :
      ( m1_subset_1('#skF_1'('#skF_5',B_55),'#skF_4')
      | v1_xboole_0('#skF_5')
      | r1_tarski('#skF_5',B_55) ) ),
    inference(resolution,[status(thm)],[c_164,c_548])).

tff(c_678,plain,(
    ! [B_113] :
      ( m1_subset_1('#skF_1'('#skF_5',B_113),'#skF_4')
      | r1_tarski('#skF_5',B_113) ) ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_552])).

tff(c_38,plain,(
    ! [D_22] :
      ( r2_hidden(D_22,'#skF_6')
      | ~ r2_hidden(D_22,'#skF_5')
      | ~ m1_subset_1(D_22,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_428,plain,(
    ! [B_93] :
      ( r2_hidden('#skF_1'('#skF_5',B_93),'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_5',B_93),'#skF_4')
      | r1_tarski('#skF_5',B_93) ) ),
    inference(resolution,[status(thm)],[c_143,c_38])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_434,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5','#skF_6'),'#skF_4')
    | r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_428,c_4])).

tff(c_444,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_434])).

tff(c_681,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_678,c_444])).

tff(c_692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_681])).

tff(c_693,plain,(
    ! [B_92] : r1_tarski('#skF_5',B_92) ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_711,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:12:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.43  
% 2.75/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.43  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 2.75/1.43  
% 2.75/1.43  %Foreground sorts:
% 2.75/1.43  
% 2.75/1.43  
% 2.75/1.43  %Background operators:
% 2.75/1.43  
% 2.75/1.43  
% 2.75/1.43  %Foreground operators:
% 2.75/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.75/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.75/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.75/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.75/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.75/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.43  
% 2.75/1.44  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 2.75/1.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.75/1.44  tff(f_37, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 2.75/1.44  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.75/1.44  tff(f_50, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 2.75/1.44  tff(f_48, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.75/1.44  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.75/1.44  tff(c_36, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.75/1.44  tff(c_143, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), A_54) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.44  tff(c_8, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.75/1.44  tff(c_168, plain, (![A_56, B_57]: (~v1_xboole_0(A_56) | r1_tarski(A_56, B_57))), inference(resolution, [status(thm)], [c_143, c_8])).
% 2.75/1.44  tff(c_177, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_168, c_36])).
% 2.75/1.44  tff(c_28, plain, (![B_17, A_16]: (m1_subset_1(B_17, A_16) | ~r2_hidden(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.75/1.44  tff(c_164, plain, (![A_54, B_55]: (m1_subset_1('#skF_1'(A_54, B_55), A_54) | v1_xboole_0(A_54) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_143, c_28])).
% 2.75/1.44  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.75/1.44  tff(c_26, plain, (![A_15]: (r1_tarski(k1_tarski(A_15), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.75/1.44  tff(c_58, plain, (![A_35, B_36]: (r2_hidden(A_35, B_36) | ~r1_tarski(k1_tarski(A_35), B_36))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.75/1.44  tff(c_63, plain, (![A_37]: (r2_hidden(A_37, k1_zfmisc_1(A_37)))), inference(resolution, [status(thm)], [c_26, c_58])).
% 2.75/1.44  tff(c_71, plain, (![A_37]: (~v1_xboole_0(k1_zfmisc_1(A_37)))), inference(resolution, [status(thm)], [c_63, c_8])).
% 2.75/1.44  tff(c_178, plain, (![B_58, A_59]: (r2_hidden(B_58, A_59) | ~m1_subset_1(B_58, A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.75/1.44  tff(c_10, plain, (![C_12, A_8]: (r1_tarski(C_12, A_8) | ~r2_hidden(C_12, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.75/1.44  tff(c_193, plain, (![B_58, A_8]: (r1_tarski(B_58, A_8) | ~m1_subset_1(B_58, k1_zfmisc_1(A_8)) | v1_xboole_0(k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_178, c_10])).
% 2.75/1.44  tff(c_204, plain, (![B_60, A_61]: (r1_tarski(B_60, A_61) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)))), inference(negUnitSimplification, [status(thm)], [c_71, c_193])).
% 2.75/1.44  tff(c_226, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_204])).
% 2.75/1.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.44  tff(c_227, plain, (![C_62, B_63, A_64]: (r2_hidden(C_62, B_63) | ~r2_hidden(C_62, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.44  tff(c_350, plain, (![A_85, B_86, B_87]: (r2_hidden('#skF_1'(A_85, B_86), B_87) | ~r1_tarski(A_85, B_87) | r1_tarski(A_85, B_86))), inference(resolution, [status(thm)], [c_6, c_227])).
% 2.75/1.44  tff(c_399, plain, (![B_90, A_91, B_92]: (~v1_xboole_0(B_90) | ~r1_tarski(A_91, B_90) | r1_tarski(A_91, B_92))), inference(resolution, [status(thm)], [c_350, c_8])).
% 2.75/1.44  tff(c_421, plain, (![B_92]: (~v1_xboole_0('#skF_4') | r1_tarski('#skF_5', B_92))), inference(resolution, [status(thm)], [c_226, c_399])).
% 2.75/1.44  tff(c_427, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_421])).
% 2.75/1.44  tff(c_30, plain, (![B_17, A_16]: (r2_hidden(B_17, A_16) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.75/1.44  tff(c_453, plain, (![B_94, B_95, A_96]: (r2_hidden(B_94, B_95) | ~r1_tarski(A_96, B_95) | ~m1_subset_1(B_94, A_96) | v1_xboole_0(A_96))), inference(resolution, [status(thm)], [c_30, c_227])).
% 2.75/1.44  tff(c_461, plain, (![B_94]: (r2_hidden(B_94, '#skF_4') | ~m1_subset_1(B_94, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_226, c_453])).
% 2.75/1.44  tff(c_489, plain, (![B_97]: (r2_hidden(B_97, '#skF_4') | ~m1_subset_1(B_97, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_177, c_461])).
% 2.75/1.44  tff(c_498, plain, (![B_97]: (m1_subset_1(B_97, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_97, '#skF_5'))), inference(resolution, [status(thm)], [c_489, c_28])).
% 2.75/1.44  tff(c_548, plain, (![B_101]: (m1_subset_1(B_101, '#skF_4') | ~m1_subset_1(B_101, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_427, c_498])).
% 2.75/1.44  tff(c_552, plain, (![B_55]: (m1_subset_1('#skF_1'('#skF_5', B_55), '#skF_4') | v1_xboole_0('#skF_5') | r1_tarski('#skF_5', B_55))), inference(resolution, [status(thm)], [c_164, c_548])).
% 2.75/1.44  tff(c_678, plain, (![B_113]: (m1_subset_1('#skF_1'('#skF_5', B_113), '#skF_4') | r1_tarski('#skF_5', B_113))), inference(negUnitSimplification, [status(thm)], [c_177, c_552])).
% 2.75/1.44  tff(c_38, plain, (![D_22]: (r2_hidden(D_22, '#skF_6') | ~r2_hidden(D_22, '#skF_5') | ~m1_subset_1(D_22, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.75/1.44  tff(c_428, plain, (![B_93]: (r2_hidden('#skF_1'('#skF_5', B_93), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_5', B_93), '#skF_4') | r1_tarski('#skF_5', B_93))), inference(resolution, [status(thm)], [c_143, c_38])).
% 2.75/1.44  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.44  tff(c_434, plain, (~m1_subset_1('#skF_1'('#skF_5', '#skF_6'), '#skF_4') | r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_428, c_4])).
% 2.75/1.44  tff(c_444, plain, (~m1_subset_1('#skF_1'('#skF_5', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_434])).
% 2.75/1.44  tff(c_681, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_678, c_444])).
% 2.75/1.44  tff(c_692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_681])).
% 2.75/1.44  tff(c_693, plain, (![B_92]: (r1_tarski('#skF_5', B_92))), inference(splitRight, [status(thm)], [c_421])).
% 2.75/1.44  tff(c_711, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_693, c_36])).
% 2.75/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.44  
% 2.75/1.44  Inference rules
% 2.75/1.44  ----------------------
% 2.75/1.44  #Ref     : 0
% 2.75/1.44  #Sup     : 137
% 2.75/1.44  #Fact    : 0
% 2.75/1.44  #Define  : 0
% 2.75/1.44  #Split   : 2
% 2.75/1.44  #Chain   : 0
% 2.75/1.44  #Close   : 0
% 2.75/1.44  
% 2.75/1.44  Ordering : KBO
% 2.75/1.44  
% 2.75/1.44  Simplification rules
% 2.75/1.44  ----------------------
% 2.75/1.44  #Subsume      : 35
% 2.75/1.44  #Demod        : 10
% 2.75/1.44  #Tautology    : 18
% 2.75/1.44  #SimpNegUnit  : 24
% 2.75/1.44  #BackRed      : 1
% 2.75/1.44  
% 2.75/1.44  #Partial instantiations: 0
% 2.75/1.44  #Strategies tried      : 1
% 2.75/1.44  
% 2.75/1.44  Timing (in seconds)
% 2.75/1.44  ----------------------
% 2.75/1.44  Preprocessing        : 0.29
% 2.75/1.44  Parsing              : 0.16
% 2.75/1.44  CNF conversion       : 0.02
% 2.75/1.44  Main loop            : 0.33
% 2.75/1.44  Inferencing          : 0.13
% 2.75/1.44  Reduction            : 0.08
% 2.75/1.44  Demodulation         : 0.05
% 2.75/1.44  BG Simplification    : 0.02
% 2.75/1.44  Subsumption          : 0.08
% 2.75/1.44  Abstraction          : 0.01
% 2.75/1.44  MUC search           : 0.00
% 2.75/1.44  Cooper               : 0.00
% 2.75/1.45  Total                : 0.65
% 2.75/1.45  Index Insertion      : 0.00
% 2.75/1.45  Index Deletion       : 0.00
% 2.75/1.45  Index Matching       : 0.00
% 2.75/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
