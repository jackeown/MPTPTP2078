%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:59 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   55 (  85 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :    6
%              Number of atoms          :   58 ( 114 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_42,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_63,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,B_66),B_66)
      | r2_hidden('#skF_2'(A_65,B_66),A_65)
      | B_66 = A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,(
    ! [C_56,B_57,A_58] :
      ( ~ v1_xboole_0(C_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(C_56))
      | ~ r2_hidden(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    ! [A_4,A_58] :
      ( ~ v1_xboole_0(A_4)
      | ~ r2_hidden(A_58,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_47])).

tff(c_51,plain,(
    ! [A_58] : ~ r2_hidden(A_58,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_70,plain,(
    ! [B_66] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_66),B_66)
      | k1_xboole_0 = B_66 ) ),
    inference(resolution,[status(thm)],[c_63,c_51])).

tff(c_139,plain,(
    ! [C_79,A_80] :
      ( r2_hidden(k4_tarski(C_79,'#skF_6'(A_80,k1_relat_1(A_80),C_79)),A_80)
      | ~ r2_hidden(C_79,k1_relat_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_168,plain,(
    ! [C_81] : ~ r2_hidden(C_81,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_139,c_51])).

tff(c_180,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_168])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_180])).

tff(c_199,plain,(
    ! [A_4] : ~ v1_xboole_0(A_4) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_2])).

tff(c_202,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_234,plain,(
    ! [A_101,B_102] :
      ( r2_hidden('#skF_1'(A_101,B_102),B_102)
      | r2_hidden('#skF_2'(A_101,B_102),A_101)
      | B_102 = A_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_209,plain,(
    ! [C_85,B_86,A_87] :
      ( ~ v1_xboole_0(C_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(C_85))
      | ~ r2_hidden(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_212,plain,(
    ! [A_4,A_87] :
      ( ~ v1_xboole_0(A_4)
      | ~ r2_hidden(A_87,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_209])).

tff(c_213,plain,(
    ! [A_87] : ~ r2_hidden(A_87,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_327,plain,(
    ! [B_110] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_110),B_110)
      | k1_xboole_0 = B_110 ) ),
    inference(resolution,[status(thm)],[c_234,c_213])).

tff(c_249,plain,(
    ! [A_103,C_104] :
      ( r2_hidden(k4_tarski('#skF_10'(A_103,k2_relat_1(A_103),C_104),C_104),A_103)
      | ~ r2_hidden(C_104,k2_relat_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_261,plain,(
    ! [C_104] : ~ r2_hidden(C_104,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_249,c_213])).

tff(c_339,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_327,c_261])).

tff(c_352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_339])).

tff(c_353,plain,(
    ! [A_4] : ~ v1_xboole_0(A_4) ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:43:16 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.27  
% 2.07/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.27  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_4 > #skF_10
% 2.15/1.27  
% 2.15/1.27  %Foreground sorts:
% 2.15/1.27  
% 2.15/1.27  
% 2.15/1.27  %Background operators:
% 2.15/1.27  
% 2.15/1.27  
% 2.15/1.27  %Foreground operators:
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.27  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.15/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.15/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.15/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.15/1.27  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.15/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.15/1.27  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.15/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.27  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 2.15/1.27  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.15/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.15/1.27  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.15/1.27  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 2.15/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.27  
% 2.15/1.28  tff(f_68, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.15/1.28  tff(f_33, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.15/1.28  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.15/1.28  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.15/1.28  tff(f_56, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.15/1.28  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.15/1.28  tff(f_64, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.15/1.28  tff(c_42, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.15/1.28  tff(c_44, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 2.15/1.28  tff(c_63, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66), B_66) | r2_hidden('#skF_2'(A_65, B_66), A_65) | B_66=A_65)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.15/1.28  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.15/1.28  tff(c_47, plain, (![C_56, B_57, A_58]: (~v1_xboole_0(C_56) | ~m1_subset_1(B_57, k1_zfmisc_1(C_56)) | ~r2_hidden(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.15/1.28  tff(c_50, plain, (![A_4, A_58]: (~v1_xboole_0(A_4) | ~r2_hidden(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_47])).
% 2.15/1.28  tff(c_51, plain, (![A_58]: (~r2_hidden(A_58, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_50])).
% 2.15/1.28  tff(c_70, plain, (![B_66]: (r2_hidden('#skF_1'(k1_xboole_0, B_66), B_66) | k1_xboole_0=B_66)), inference(resolution, [status(thm)], [c_63, c_51])).
% 2.15/1.28  tff(c_139, plain, (![C_79, A_80]: (r2_hidden(k4_tarski(C_79, '#skF_6'(A_80, k1_relat_1(A_80), C_79)), A_80) | ~r2_hidden(C_79, k1_relat_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.15/1.28  tff(c_168, plain, (![C_81]: (~r2_hidden(C_81, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_139, c_51])).
% 2.15/1.28  tff(c_180, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_168])).
% 2.15/1.28  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_180])).
% 2.15/1.28  tff(c_199, plain, (![A_4]: (~v1_xboole_0(A_4))), inference(splitRight, [status(thm)], [c_50])).
% 2.15/1.28  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.15/1.28  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_199, c_2])).
% 2.15/1.28  tff(c_202, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.15/1.28  tff(c_234, plain, (![A_101, B_102]: (r2_hidden('#skF_1'(A_101, B_102), B_102) | r2_hidden('#skF_2'(A_101, B_102), A_101) | B_102=A_101)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.15/1.28  tff(c_209, plain, (![C_85, B_86, A_87]: (~v1_xboole_0(C_85) | ~m1_subset_1(B_86, k1_zfmisc_1(C_85)) | ~r2_hidden(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.15/1.28  tff(c_212, plain, (![A_4, A_87]: (~v1_xboole_0(A_4) | ~r2_hidden(A_87, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_209])).
% 2.15/1.28  tff(c_213, plain, (![A_87]: (~r2_hidden(A_87, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_212])).
% 2.15/1.28  tff(c_327, plain, (![B_110]: (r2_hidden('#skF_1'(k1_xboole_0, B_110), B_110) | k1_xboole_0=B_110)), inference(resolution, [status(thm)], [c_234, c_213])).
% 2.15/1.28  tff(c_249, plain, (![A_103, C_104]: (r2_hidden(k4_tarski('#skF_10'(A_103, k2_relat_1(A_103), C_104), C_104), A_103) | ~r2_hidden(C_104, k2_relat_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.15/1.28  tff(c_261, plain, (![C_104]: (~r2_hidden(C_104, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_249, c_213])).
% 2.15/1.28  tff(c_339, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_327, c_261])).
% 2.15/1.28  tff(c_352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_202, c_339])).
% 2.15/1.28  tff(c_353, plain, (![A_4]: (~v1_xboole_0(A_4))), inference(splitRight, [status(thm)], [c_212])).
% 2.15/1.28  tff(c_355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_353, c_2])).
% 2.15/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.28  
% 2.15/1.28  Inference rules
% 2.15/1.28  ----------------------
% 2.15/1.28  #Ref     : 0
% 2.15/1.28  #Sup     : 57
% 2.15/1.28  #Fact    : 0
% 2.15/1.28  #Define  : 0
% 2.15/1.28  #Split   : 3
% 2.15/1.28  #Chain   : 0
% 2.15/1.28  #Close   : 0
% 2.15/1.29  
% 2.15/1.29  Ordering : KBO
% 2.15/1.29  
% 2.15/1.29  Simplification rules
% 2.15/1.29  ----------------------
% 2.15/1.29  #Subsume      : 13
% 2.15/1.29  #Demod        : 2
% 2.15/1.29  #Tautology    : 12
% 2.15/1.29  #SimpNegUnit  : 5
% 2.15/1.29  #BackRed      : 3
% 2.15/1.29  
% 2.15/1.29  #Partial instantiations: 0
% 2.15/1.29  #Strategies tried      : 1
% 2.15/1.29  
% 2.15/1.29  Timing (in seconds)
% 2.15/1.29  ----------------------
% 2.15/1.29  Preprocessing        : 0.28
% 2.15/1.29  Parsing              : 0.15
% 2.15/1.29  CNF conversion       : 0.02
% 2.15/1.29  Main loop            : 0.22
% 2.15/1.29  Inferencing          : 0.09
% 2.15/1.29  Reduction            : 0.05
% 2.15/1.29  Demodulation         : 0.03
% 2.15/1.29  BG Simplification    : 0.01
% 2.15/1.29  Subsumption          : 0.04
% 2.15/1.29  Abstraction          : 0.01
% 2.15/1.29  MUC search           : 0.00
% 2.15/1.29  Cooper               : 0.00
% 2.15/1.29  Total                : 0.52
% 2.15/1.29  Index Insertion      : 0.00
% 2.15/1.29  Index Deletion       : 0.00
% 2.15/1.29  Index Matching       : 0.00
% 2.15/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
