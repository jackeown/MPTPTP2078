%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:49 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 141 expanded)
%              Number of leaves         :   23 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  116 ( 310 expanded)
%              Number of equality atoms :    7 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_74,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r2_xboole_0(A,B)
        & r1_tarski(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_42,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_xboole_0(A_10,B_11)
      | B_11 = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_40,plain,(
    ! [A_22] : ~ v1_xboole_0(k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_292,plain,(
    ! [B_72,A_73] :
      ( r2_hidden(B_72,A_73)
      | ~ m1_subset_1(B_72,A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [C_19,A_15] :
      ( r1_tarski(C_19,A_15)
      | ~ r2_hidden(C_19,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_299,plain,(
    ! [B_72,A_15] :
      ( r1_tarski(B_72,A_15)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15)) ) ),
    inference(resolution,[status(thm)],[c_292,c_20])).

tff(c_308,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(B_74,A_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_299])).

tff(c_328,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_308])).

tff(c_371,plain,(
    ! [A_84,C_85,B_86] :
      ( r2_xboole_0(A_84,C_85)
      | ~ r1_tarski(B_86,C_85)
      | ~ r2_xboole_0(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_384,plain,(
    ! [A_87] :
      ( r2_xboole_0(A_87,'#skF_5')
      | ~ r2_xboole_0(A_87,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_328,c_371])).

tff(c_14,plain,(
    ! [B_11] : ~ r2_xboole_0(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_393,plain,(
    ~ r2_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_384,c_14])).

tff(c_412,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_393])).

tff(c_415,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_412])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [B_42,A_43] :
      ( m1_subset_1(B_42,A_43)
      | ~ r2_hidden(B_42,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_104,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_50,plain,(
    ! [C_29] :
      ( r2_hidden(C_29,'#skF_6')
      | ~ m1_subset_1(C_29,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [C_29] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_29,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_55,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_44,plain,(
    ! [C_24] :
      ( r2_hidden(C_24,'#skF_6')
      | ~ m1_subset_1(C_24,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_100,plain,(
    ! [C_24] :
      ( m1_subset_1(C_24,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_24,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_91])).

tff(c_113,plain,(
    ! [C_45] :
      ( m1_subset_1(C_45,'#skF_6')
      | ~ m1_subset_1(C_45,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_100])).

tff(c_122,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_104,c_113])).

tff(c_124,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_163,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_2'(A_53,B_54),A_53)
      | r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_181,plain,(
    ! [A_53,B_54] :
      ( ~ v1_xboole_0(A_53)
      | r1_tarski(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_192,plain,(
    ! [B_60,A_61] :
      ( r2_hidden(B_60,A_61)
      | ~ m1_subset_1(B_60,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_203,plain,(
    ! [B_60,A_15] :
      ( r1_tarski(B_60,A_15)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15)) ) ),
    inference(resolution,[status(thm)],[c_192,c_20])).

tff(c_213,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(B_62,A_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_203])).

tff(c_233,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_213])).

tff(c_18,plain,(
    ! [A_12,C_14,B_13] :
      ( r2_xboole_0(A_12,C_14)
      | ~ r1_tarski(B_13,C_14)
      | ~ r2_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_247,plain,(
    ! [A_67] :
      ( r2_xboole_0(A_67,'#skF_5')
      | ~ r2_xboole_0(A_67,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_233,c_18])).

tff(c_256,plain,(
    ~ r2_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_247,c_14])).

tff(c_259,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_256])).

tff(c_262,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_259])).

tff(c_265,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_181,c_262])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_265])).

tff(c_271,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_329,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_2'(A_76,B_77),A_76)
      | r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    ! [B_21,A_20] :
      ( m1_subset_1(B_21,A_20)
      | ~ r2_hidden(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_652,plain,(
    ! [A_123,B_124] :
      ( m1_subset_1('#skF_2'(A_123,B_124),A_123)
      | v1_xboole_0(A_123)
      | r1_tarski(A_123,B_124) ) ),
    inference(resolution,[status(thm)],[c_329,c_32])).

tff(c_343,plain,(
    ! [A_78,B_79] :
      ( ~ r2_hidden('#skF_2'(A_78,B_79),B_79)
      | r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_363,plain,(
    ! [A_78] :
      ( r1_tarski(A_78,'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_78,'#skF_6'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_343])).

tff(c_660,plain,
    ( v1_xboole_0('#skF_5')
    | r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_652,c_363])).

tff(c_677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_415,c_271,c_415,c_660])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.33  
% 2.60/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.33  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.60/1.33  
% 2.60/1.33  %Foreground sorts:
% 2.60/1.33  
% 2.60/1.33  
% 2.60/1.33  %Background operators:
% 2.60/1.33  
% 2.60/1.33  
% 2.60/1.33  %Foreground operators:
% 2.60/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.60/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.60/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.60/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.60/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.60/1.33  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.60/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.60/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.60/1.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.60/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.33  
% 2.60/1.35  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 2.60/1.35  tff(f_45, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.60/1.35  tff(f_74, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.60/1.35  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.60/1.35  tff(f_58, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.60/1.35  tff(f_51, axiom, (![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_xboole_1)).
% 2.60/1.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.60/1.35  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.60/1.35  tff(c_42, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.60/1.35  tff(c_12, plain, (![A_10, B_11]: (r2_xboole_0(A_10, B_11) | B_11=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.60/1.35  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.60/1.35  tff(c_40, plain, (![A_22]: (~v1_xboole_0(k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.60/1.35  tff(c_292, plain, (![B_72, A_73]: (r2_hidden(B_72, A_73) | ~m1_subset_1(B_72, A_73) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.60/1.35  tff(c_20, plain, (![C_19, A_15]: (r1_tarski(C_19, A_15) | ~r2_hidden(C_19, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.60/1.35  tff(c_299, plain, (![B_72, A_15]: (r1_tarski(B_72, A_15) | ~m1_subset_1(B_72, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)))), inference(resolution, [status(thm)], [c_292, c_20])).
% 2.60/1.35  tff(c_308, plain, (![B_74, A_75]: (r1_tarski(B_74, A_75) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)))), inference(negUnitSimplification, [status(thm)], [c_40, c_299])).
% 2.60/1.35  tff(c_328, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_308])).
% 2.60/1.35  tff(c_371, plain, (![A_84, C_85, B_86]: (r2_xboole_0(A_84, C_85) | ~r1_tarski(B_86, C_85) | ~r2_xboole_0(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.60/1.35  tff(c_384, plain, (![A_87]: (r2_xboole_0(A_87, '#skF_5') | ~r2_xboole_0(A_87, '#skF_6'))), inference(resolution, [status(thm)], [c_328, c_371])).
% 2.60/1.35  tff(c_14, plain, (![B_11]: (~r2_xboole_0(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.60/1.35  tff(c_393, plain, (~r2_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_384, c_14])).
% 2.60/1.35  tff(c_412, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_12, c_393])).
% 2.60/1.35  tff(c_415, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_42, c_412])).
% 2.60/1.35  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.35  tff(c_91, plain, (![B_42, A_43]: (m1_subset_1(B_42, A_43) | ~r2_hidden(B_42, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.60/1.35  tff(c_104, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_91])).
% 2.60/1.35  tff(c_50, plain, (![C_29]: (r2_hidden(C_29, '#skF_6') | ~m1_subset_1(C_29, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.60/1.35  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.35  tff(c_54, plain, (![C_29]: (~v1_xboole_0('#skF_6') | ~m1_subset_1(C_29, '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_2])).
% 2.60/1.35  tff(c_55, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_54])).
% 2.60/1.35  tff(c_44, plain, (![C_24]: (r2_hidden(C_24, '#skF_6') | ~m1_subset_1(C_24, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.60/1.35  tff(c_100, plain, (![C_24]: (m1_subset_1(C_24, '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(C_24, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_91])).
% 2.60/1.35  tff(c_113, plain, (![C_45]: (m1_subset_1(C_45, '#skF_6') | ~m1_subset_1(C_45, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_55, c_100])).
% 2.60/1.35  tff(c_122, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_104, c_113])).
% 2.60/1.35  tff(c_124, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_122])).
% 2.60/1.35  tff(c_163, plain, (![A_53, B_54]: (r2_hidden('#skF_2'(A_53, B_54), A_53) | r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.60/1.35  tff(c_181, plain, (![A_53, B_54]: (~v1_xboole_0(A_53) | r1_tarski(A_53, B_54))), inference(resolution, [status(thm)], [c_163, c_2])).
% 2.60/1.35  tff(c_192, plain, (![B_60, A_61]: (r2_hidden(B_60, A_61) | ~m1_subset_1(B_60, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.60/1.35  tff(c_203, plain, (![B_60, A_15]: (r1_tarski(B_60, A_15) | ~m1_subset_1(B_60, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)))), inference(resolution, [status(thm)], [c_192, c_20])).
% 2.60/1.35  tff(c_213, plain, (![B_62, A_63]: (r1_tarski(B_62, A_63) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)))), inference(negUnitSimplification, [status(thm)], [c_40, c_203])).
% 2.60/1.35  tff(c_233, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_213])).
% 2.60/1.35  tff(c_18, plain, (![A_12, C_14, B_13]: (r2_xboole_0(A_12, C_14) | ~r1_tarski(B_13, C_14) | ~r2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.60/1.35  tff(c_247, plain, (![A_67]: (r2_xboole_0(A_67, '#skF_5') | ~r2_xboole_0(A_67, '#skF_6'))), inference(resolution, [status(thm)], [c_233, c_18])).
% 2.60/1.35  tff(c_256, plain, (~r2_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_247, c_14])).
% 2.60/1.35  tff(c_259, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_12, c_256])).
% 2.60/1.35  tff(c_262, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_42, c_259])).
% 2.60/1.35  tff(c_265, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_181, c_262])).
% 2.60/1.35  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_265])).
% 2.60/1.35  tff(c_271, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_122])).
% 2.60/1.35  tff(c_329, plain, (![A_76, B_77]: (r2_hidden('#skF_2'(A_76, B_77), A_76) | r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.60/1.35  tff(c_32, plain, (![B_21, A_20]: (m1_subset_1(B_21, A_20) | ~r2_hidden(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.60/1.35  tff(c_652, plain, (![A_123, B_124]: (m1_subset_1('#skF_2'(A_123, B_124), A_123) | v1_xboole_0(A_123) | r1_tarski(A_123, B_124))), inference(resolution, [status(thm)], [c_329, c_32])).
% 2.60/1.35  tff(c_343, plain, (![A_78, B_79]: (~r2_hidden('#skF_2'(A_78, B_79), B_79) | r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.60/1.35  tff(c_363, plain, (![A_78]: (r1_tarski(A_78, '#skF_6') | ~m1_subset_1('#skF_2'(A_78, '#skF_6'), '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_343])).
% 2.60/1.35  tff(c_660, plain, (v1_xboole_0('#skF_5') | r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_652, c_363])).
% 2.60/1.35  tff(c_677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_415, c_271, c_415, c_660])).
% 2.60/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.35  
% 2.60/1.35  Inference rules
% 2.60/1.35  ----------------------
% 2.60/1.35  #Ref     : 0
% 2.60/1.35  #Sup     : 125
% 2.60/1.35  #Fact    : 0
% 2.60/1.35  #Define  : 0
% 2.60/1.35  #Split   : 4
% 2.60/1.35  #Chain   : 0
% 2.60/1.35  #Close   : 0
% 2.60/1.35  
% 2.60/1.35  Ordering : KBO
% 2.60/1.35  
% 2.60/1.35  Simplification rules
% 2.60/1.35  ----------------------
% 2.60/1.35  #Subsume      : 26
% 2.60/1.35  #Demod        : 9
% 2.60/1.35  #Tautology    : 24
% 2.60/1.35  #SimpNegUnit  : 15
% 2.60/1.35  #BackRed      : 0
% 2.60/1.35  
% 2.60/1.35  #Partial instantiations: 0
% 2.60/1.35  #Strategies tried      : 1
% 2.60/1.35  
% 2.60/1.35  Timing (in seconds)
% 2.60/1.35  ----------------------
% 2.60/1.35  Preprocessing        : 0.29
% 2.60/1.35  Parsing              : 0.15
% 2.60/1.35  CNF conversion       : 0.02
% 2.60/1.35  Main loop            : 0.30
% 2.60/1.35  Inferencing          : 0.12
% 2.60/1.35  Reduction            : 0.07
% 2.60/1.35  Demodulation         : 0.04
% 2.60/1.35  BG Simplification    : 0.02
% 2.60/1.35  Subsumption          : 0.07
% 2.60/1.35  Abstraction          : 0.01
% 2.60/1.35  MUC search           : 0.00
% 2.60/1.35  Cooper               : 0.00
% 2.60/1.35  Total                : 0.62
% 2.60/1.35  Index Insertion      : 0.00
% 2.60/1.35  Index Deletion       : 0.00
% 2.60/1.35  Index Matching       : 0.00
% 2.60/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
