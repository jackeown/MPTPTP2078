%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:41 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   46 (  74 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 147 expanded)
%              Number of equality atoms :   23 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_42,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    ! [A_13] : k2_subset_1(A_13) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [A_14] : m1_subset_1(k2_subset_1(A_14),k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_37,plain,(
    ! [A_14] : m1_subset_1(A_14,k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_214,plain,(
    ! [A_49,B_50,C_51] :
      ( k4_subset_1(A_49,B_50,C_51) = k2_xboole_0(B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_221,plain,(
    ! [A_52,B_53] :
      ( k4_subset_1(A_52,B_53,A_52) = k2_xboole_0(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(resolution,[status(thm)],[c_37,c_214])).

tff(c_227,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_221])).

tff(c_34,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_34])).

tff(c_235,plain,(
    k2_xboole_0('#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_38])).

tff(c_490,plain,(
    ! [A_82,B_83,C_84] :
      ( r2_hidden('#skF_1'(A_82,B_83,C_84),B_83)
      | r2_hidden('#skF_1'(A_82,B_83,C_84),A_82)
      | r2_hidden('#skF_2'(A_82,B_83,C_84),C_84)
      | k2_xboole_0(A_82,B_83) = C_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_810,plain,(
    ! [A_102,B_103] :
      ( r2_hidden('#skF_1'(A_102,B_103,B_103),A_102)
      | r2_hidden('#skF_2'(A_102,B_103,B_103),B_103)
      | k2_xboole_0(A_102,B_103) = B_103 ) ),
    inference(resolution,[status(thm)],[c_490,c_16])).

tff(c_318,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden('#skF_1'(A_73,B_74,C_75),B_74)
      | r2_hidden('#skF_1'(A_73,B_74,C_75),A_73)
      | ~ r2_hidden('#skF_2'(A_73,B_74,C_75),B_74)
      | k2_xboole_0(A_73,B_74) = C_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_360,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_1'(A_73,B_74,B_74),A_73)
      | ~ r2_hidden('#skF_2'(A_73,B_74,B_74),B_74)
      | k2_xboole_0(A_73,B_74) = B_74 ) ),
    inference(resolution,[status(thm)],[c_318,c_8])).

tff(c_856,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_1'(A_104,B_105,B_105),A_104)
      | k2_xboole_0(A_104,B_105) = B_105 ) ),
    inference(resolution,[status(thm)],[c_810,c_360])).

tff(c_30,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_917,plain,(
    ! [A_109,B_110,A_111] :
      ( r2_hidden('#skF_1'(A_109,B_110,B_110),A_111)
      | ~ m1_subset_1(A_109,k1_zfmisc_1(A_111))
      | k2_xboole_0(A_109,B_110) = B_110 ) ),
    inference(resolution,[status(thm)],[c_856,c_30])).

tff(c_940,plain,(
    ! [A_109,A_111] :
      ( r2_hidden('#skF_2'(A_109,A_111,A_111),A_111)
      | ~ m1_subset_1(A_109,k1_zfmisc_1(A_111))
      | k2_xboole_0(A_109,A_111) = A_111 ) ),
    inference(resolution,[status(thm)],[c_917,c_16])).

tff(c_1082,plain,(
    ! [A_122,A_123] :
      ( ~ r2_hidden('#skF_2'(A_122,A_123,A_123),A_123)
      | ~ m1_subset_1(A_122,k1_zfmisc_1(A_123))
      | k2_xboole_0(A_122,A_123) = A_123 ) ),
    inference(resolution,[status(thm)],[c_917,c_8])).

tff(c_1133,plain,(
    ! [A_126,A_127] :
      ( ~ m1_subset_1(A_126,k1_zfmisc_1(A_127))
      | k2_xboole_0(A_126,A_127) = A_127 ) ),
    inference(resolution,[status(thm)],[c_940,c_1082])).

tff(c_1139,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_1133])).

tff(c_1145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_1139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:12:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.53  
% 3.24/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.53  %$ r2_hidden > m1_subset_1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.24/1.53  
% 3.24/1.53  %Foreground sorts:
% 3.24/1.53  
% 3.24/1.53  
% 3.24/1.53  %Background operators:
% 3.24/1.53  
% 3.24/1.53  
% 3.24/1.53  %Foreground operators:
% 3.24/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.24/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.24/1.53  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.24/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.24/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.24/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.24/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.24/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.24/1.53  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.24/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.53  
% 3.24/1.54  tff(f_62, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 3.24/1.54  tff(f_42, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.24/1.54  tff(f_44, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.24/1.54  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.24/1.54  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.24/1.54  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.24/1.54  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.24/1.54  tff(c_26, plain, (![A_13]: (k2_subset_1(A_13)=A_13)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.24/1.54  tff(c_28, plain, (![A_14]: (m1_subset_1(k2_subset_1(A_14), k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.24/1.54  tff(c_37, plain, (![A_14]: (m1_subset_1(A_14, k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 3.24/1.54  tff(c_214, plain, (![A_49, B_50, C_51]: (k4_subset_1(A_49, B_50, C_51)=k2_xboole_0(B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)) | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.24/1.54  tff(c_221, plain, (![A_52, B_53]: (k4_subset_1(A_52, B_53, A_52)=k2_xboole_0(B_53, A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(resolution, [status(thm)], [c_37, c_214])).
% 3.24/1.54  tff(c_227, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_221])).
% 3.24/1.54  tff(c_34, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.24/1.54  tff(c_38, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_34])).
% 3.24/1.54  tff(c_235, plain, (k2_xboole_0('#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_227, c_38])).
% 3.24/1.54  tff(c_490, plain, (![A_82, B_83, C_84]: (r2_hidden('#skF_1'(A_82, B_83, C_84), B_83) | r2_hidden('#skF_1'(A_82, B_83, C_84), A_82) | r2_hidden('#skF_2'(A_82, B_83, C_84), C_84) | k2_xboole_0(A_82, B_83)=C_84)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.24/1.54  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.24/1.54  tff(c_810, plain, (![A_102, B_103]: (r2_hidden('#skF_1'(A_102, B_103, B_103), A_102) | r2_hidden('#skF_2'(A_102, B_103, B_103), B_103) | k2_xboole_0(A_102, B_103)=B_103)), inference(resolution, [status(thm)], [c_490, c_16])).
% 3.24/1.54  tff(c_318, plain, (![A_73, B_74, C_75]: (r2_hidden('#skF_1'(A_73, B_74, C_75), B_74) | r2_hidden('#skF_1'(A_73, B_74, C_75), A_73) | ~r2_hidden('#skF_2'(A_73, B_74, C_75), B_74) | k2_xboole_0(A_73, B_74)=C_75)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.24/1.54  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.24/1.54  tff(c_360, plain, (![A_73, B_74]: (r2_hidden('#skF_1'(A_73, B_74, B_74), A_73) | ~r2_hidden('#skF_2'(A_73, B_74, B_74), B_74) | k2_xboole_0(A_73, B_74)=B_74)), inference(resolution, [status(thm)], [c_318, c_8])).
% 3.24/1.54  tff(c_856, plain, (![A_104, B_105]: (r2_hidden('#skF_1'(A_104, B_105, B_105), A_104) | k2_xboole_0(A_104, B_105)=B_105)), inference(resolution, [status(thm)], [c_810, c_360])).
% 3.24/1.54  tff(c_30, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.24/1.54  tff(c_917, plain, (![A_109, B_110, A_111]: (r2_hidden('#skF_1'(A_109, B_110, B_110), A_111) | ~m1_subset_1(A_109, k1_zfmisc_1(A_111)) | k2_xboole_0(A_109, B_110)=B_110)), inference(resolution, [status(thm)], [c_856, c_30])).
% 3.24/1.54  tff(c_940, plain, (![A_109, A_111]: (r2_hidden('#skF_2'(A_109, A_111, A_111), A_111) | ~m1_subset_1(A_109, k1_zfmisc_1(A_111)) | k2_xboole_0(A_109, A_111)=A_111)), inference(resolution, [status(thm)], [c_917, c_16])).
% 3.24/1.54  tff(c_1082, plain, (![A_122, A_123]: (~r2_hidden('#skF_2'(A_122, A_123, A_123), A_123) | ~m1_subset_1(A_122, k1_zfmisc_1(A_123)) | k2_xboole_0(A_122, A_123)=A_123)), inference(resolution, [status(thm)], [c_917, c_8])).
% 3.24/1.54  tff(c_1133, plain, (![A_126, A_127]: (~m1_subset_1(A_126, k1_zfmisc_1(A_127)) | k2_xboole_0(A_126, A_127)=A_127)), inference(resolution, [status(thm)], [c_940, c_1082])).
% 3.24/1.54  tff(c_1139, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_36, c_1133])).
% 3.24/1.54  tff(c_1145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_235, c_1139])).
% 3.24/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.54  
% 3.24/1.54  Inference rules
% 3.24/1.54  ----------------------
% 3.24/1.54  #Ref     : 0
% 3.24/1.54  #Sup     : 236
% 3.24/1.54  #Fact    : 6
% 3.24/1.54  #Define  : 0
% 3.24/1.54  #Split   : 0
% 3.24/1.54  #Chain   : 0
% 3.24/1.54  #Close   : 0
% 3.24/1.54  
% 3.24/1.54  Ordering : KBO
% 3.24/1.54  
% 3.24/1.54  Simplification rules
% 3.24/1.54  ----------------------
% 3.24/1.54  #Subsume      : 40
% 3.24/1.54  #Demod        : 47
% 3.24/1.54  #Tautology    : 78
% 3.24/1.54  #SimpNegUnit  : 1
% 3.24/1.54  #BackRed      : 4
% 3.24/1.54  
% 3.24/1.54  #Partial instantiations: 0
% 3.24/1.54  #Strategies tried      : 1
% 3.24/1.54  
% 3.24/1.54  Timing (in seconds)
% 3.24/1.54  ----------------------
% 3.49/1.54  Preprocessing        : 0.31
% 3.49/1.54  Parsing              : 0.16
% 3.49/1.54  CNF conversion       : 0.02
% 3.49/1.54  Main loop            : 0.47
% 3.49/1.54  Inferencing          : 0.17
% 3.49/1.54  Reduction            : 0.14
% 3.49/1.54  Demodulation         : 0.11
% 3.49/1.54  BG Simplification    : 0.02
% 3.49/1.54  Subsumption          : 0.11
% 3.49/1.54  Abstraction          : 0.03
% 3.49/1.55  MUC search           : 0.00
% 3.49/1.55  Cooper               : 0.00
% 3.49/1.55  Total                : 0.81
% 3.49/1.55  Index Insertion      : 0.00
% 3.49/1.55  Index Deletion       : 0.00
% 3.49/1.55  Index Matching       : 0.00
% 3.49/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
