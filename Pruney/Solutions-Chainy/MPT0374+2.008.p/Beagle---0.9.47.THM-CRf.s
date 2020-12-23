%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:00 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 145 expanded)
%              Number of leaves         :   23 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :   91 ( 322 expanded)
%              Number of equality atoms :    6 (  22 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ! [C] :
            ( m1_subset_1(C,A)
           => ( A != k1_xboole_0
             => m1_subset_1(k2_tarski(B,C),k1_zfmisc_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_56,plain,(
    ! [B_27,A_28] :
      ( v1_xboole_0(B_27)
      | ~ m1_subset_1(B_27,A_28)
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_63,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_56])).

tff(c_65,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_280,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_tarski(k2_tarski(A_66,B_67),C_68)
      | ~ r2_hidden(B_67,C_68)
      | ~ r2_hidden(A_66,C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    m1_subset_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( r2_hidden(B_17,A_16)
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_128,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(k2_tarski(A_47,B_48),C_49)
      | ~ r2_hidden(B_48,C_49)
      | ~ r2_hidden(A_47,C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_76,plain,(
    ! [B_31,A_32] :
      ( m1_subset_1(B_31,A_32)
      | ~ v1_xboole_0(B_31)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    ~ m1_subset_1(k2_tarski('#skF_5','#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_84,plain,
    ( ~ v1_xboole_0(k2_tarski('#skF_5','#skF_6'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_36])).

tff(c_95,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_12,plain,(
    ! [C_12,A_8] :
      ( r2_hidden(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,(
    ! [B_35,A_36] :
      ( m1_subset_1(B_35,A_36)
      | ~ r2_hidden(B_35,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_117,plain,(
    ! [C_45,A_46] :
      ( m1_subset_1(C_45,k1_zfmisc_1(A_46))
      | v1_xboole_0(k1_zfmisc_1(A_46))
      | ~ r1_tarski(C_45,A_46) ) ),
    inference(resolution,[status(thm)],[c_12,c_96])).

tff(c_123,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski(k2_tarski('#skF_5','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_117,c_36])).

tff(c_127,plain,(
    ~ r1_tarski(k2_tarski('#skF_5','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_123])).

tff(c_138,plain,
    ( ~ r2_hidden('#skF_6','#skF_4')
    | ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_127])).

tff(c_141,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_144,plain,
    ( ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_141])).

tff(c_147,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_144])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_147])).

tff(c_150,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_164,plain,
    ( ~ m1_subset_1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_150])).

tff(c_167,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_164])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_167])).

tff(c_171,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_50,plain,(
    ! [C_23,A_24] :
      ( r2_hidden(C_23,k1_zfmisc_1(A_24))
      | ~ r1_tarski(C_23,A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [A_24,C_23] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_24))
      | ~ r1_tarski(C_23,A_24) ) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_177,plain,(
    ! [C_23] : ~ r1_tarski(C_23,'#skF_4') ),
    inference(resolution,[status(thm)],[c_171,c_54])).

tff(c_293,plain,(
    ! [B_67,A_66] :
      ( ~ r2_hidden(B_67,'#skF_4')
      | ~ r2_hidden(A_66,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_280,c_177])).

tff(c_304,plain,(
    ! [A_71] : ~ r2_hidden(A_71,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_312,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_304])).

tff(c_319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_312])).

tff(c_321,plain,(
    ! [B_72] : ~ r2_hidden(B_72,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_329,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_321])).

tff(c_336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_329])).

tff(c_338,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_346,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_338,c_6])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:15:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.52  
% 2.24/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.53  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.24/1.53  
% 2.24/1.53  %Foreground sorts:
% 2.24/1.53  
% 2.24/1.53  
% 2.24/1.53  %Background operators:
% 2.24/1.53  
% 2.24/1.53  
% 2.24/1.53  %Foreground operators:
% 2.24/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.24/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.24/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.53  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.53  tff('#skF_6', type, '#skF_6': $i).
% 2.24/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.53  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.24/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.53  
% 2.43/1.54  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (~(A = k1_xboole_0) => m1_subset_1(k2_tarski(B, C), k1_zfmisc_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_subset_1)).
% 2.43/1.54  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.43/1.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.43/1.54  tff(f_50, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.43/1.54  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.43/1.54  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.43/1.54  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.43/1.54  tff(c_42, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.43/1.54  tff(c_56, plain, (![B_27, A_28]: (v1_xboole_0(B_27) | ~m1_subset_1(B_27, A_28) | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.43/1.54  tff(c_63, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_56])).
% 2.43/1.54  tff(c_65, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_63])).
% 2.43/1.54  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.54  tff(c_280, plain, (![A_66, B_67, C_68]: (r1_tarski(k2_tarski(A_66, B_67), C_68) | ~r2_hidden(B_67, C_68) | ~r2_hidden(A_66, C_68))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.43/1.54  tff(c_40, plain, (m1_subset_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.43/1.54  tff(c_30, plain, (![B_17, A_16]: (r2_hidden(B_17, A_16) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.43/1.54  tff(c_128, plain, (![A_47, B_48, C_49]: (r1_tarski(k2_tarski(A_47, B_48), C_49) | ~r2_hidden(B_48, C_49) | ~r2_hidden(A_47, C_49))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.43/1.54  tff(c_76, plain, (![B_31, A_32]: (m1_subset_1(B_31, A_32) | ~v1_xboole_0(B_31) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.43/1.54  tff(c_36, plain, (~m1_subset_1(k2_tarski('#skF_5', '#skF_6'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.43/1.54  tff(c_84, plain, (~v1_xboole_0(k2_tarski('#skF_5', '#skF_6')) | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_36])).
% 2.43/1.54  tff(c_95, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_84])).
% 2.43/1.54  tff(c_12, plain, (![C_12, A_8]: (r2_hidden(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.43/1.54  tff(c_96, plain, (![B_35, A_36]: (m1_subset_1(B_35, A_36) | ~r2_hidden(B_35, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.43/1.54  tff(c_117, plain, (![C_45, A_46]: (m1_subset_1(C_45, k1_zfmisc_1(A_46)) | v1_xboole_0(k1_zfmisc_1(A_46)) | ~r1_tarski(C_45, A_46))), inference(resolution, [status(thm)], [c_12, c_96])).
% 2.43/1.54  tff(c_123, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_tarski('#skF_5', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_117, c_36])).
% 2.43/1.54  tff(c_127, plain, (~r1_tarski(k2_tarski('#skF_5', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_95, c_123])).
% 2.43/1.54  tff(c_138, plain, (~r2_hidden('#skF_6', '#skF_4') | ~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_128, c_127])).
% 2.43/1.54  tff(c_141, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_138])).
% 2.43/1.54  tff(c_144, plain, (~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_141])).
% 2.43/1.54  tff(c_147, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_144])).
% 2.43/1.54  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_147])).
% 2.43/1.54  tff(c_150, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_138])).
% 2.43/1.54  tff(c_164, plain, (~m1_subset_1('#skF_6', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_150])).
% 2.43/1.54  tff(c_167, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_164])).
% 2.43/1.54  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_167])).
% 2.43/1.54  tff(c_171, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_84])).
% 2.43/1.54  tff(c_50, plain, (![C_23, A_24]: (r2_hidden(C_23, k1_zfmisc_1(A_24)) | ~r1_tarski(C_23, A_24))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.43/1.54  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.54  tff(c_54, plain, (![A_24, C_23]: (~v1_xboole_0(k1_zfmisc_1(A_24)) | ~r1_tarski(C_23, A_24))), inference(resolution, [status(thm)], [c_50, c_2])).
% 2.43/1.54  tff(c_177, plain, (![C_23]: (~r1_tarski(C_23, '#skF_4'))), inference(resolution, [status(thm)], [c_171, c_54])).
% 2.43/1.54  tff(c_293, plain, (![B_67, A_66]: (~r2_hidden(B_67, '#skF_4') | ~r2_hidden(A_66, '#skF_4'))), inference(resolution, [status(thm)], [c_280, c_177])).
% 2.43/1.54  tff(c_304, plain, (![A_71]: (~r2_hidden(A_71, '#skF_4'))), inference(splitLeft, [status(thm)], [c_293])).
% 2.43/1.54  tff(c_312, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_304])).
% 2.43/1.54  tff(c_319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_312])).
% 2.43/1.54  tff(c_321, plain, (![B_72]: (~r2_hidden(B_72, '#skF_4'))), inference(splitRight, [status(thm)], [c_293])).
% 2.43/1.54  tff(c_329, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_321])).
% 2.43/1.54  tff(c_336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_329])).
% 2.43/1.54  tff(c_338, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_63])).
% 2.43/1.54  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.43/1.54  tff(c_346, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_338, c_6])).
% 2.43/1.54  tff(c_350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_346])).
% 2.43/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.54  
% 2.43/1.54  Inference rules
% 2.43/1.54  ----------------------
% 2.43/1.54  #Ref     : 0
% 2.43/1.54  #Sup     : 57
% 2.43/1.54  #Fact    : 0
% 2.43/1.54  #Define  : 0
% 2.43/1.54  #Split   : 5
% 2.43/1.54  #Chain   : 0
% 2.43/1.54  #Close   : 0
% 2.43/1.54  
% 2.43/1.54  Ordering : KBO
% 2.43/1.54  
% 2.43/1.54  Simplification rules
% 2.43/1.54  ----------------------
% 2.43/1.54  #Subsume      : 9
% 2.43/1.54  #Demod        : 16
% 2.43/1.54  #Tautology    : 25
% 2.43/1.54  #SimpNegUnit  : 12
% 2.43/1.54  #BackRed      : 2
% 2.43/1.54  
% 2.43/1.54  #Partial instantiations: 0
% 2.43/1.54  #Strategies tried      : 1
% 2.43/1.54  
% 2.43/1.54  Timing (in seconds)
% 2.43/1.54  ----------------------
% 2.43/1.54  Preprocessing        : 0.40
% 2.43/1.54  Parsing              : 0.21
% 2.43/1.54  CNF conversion       : 0.03
% 2.43/1.54  Main loop            : 0.24
% 2.43/1.54  Inferencing          : 0.09
% 2.43/1.54  Reduction            : 0.06
% 2.43/1.54  Demodulation         : 0.04
% 2.43/1.54  BG Simplification    : 0.02
% 2.43/1.54  Subsumption          : 0.04
% 2.43/1.54  Abstraction          : 0.01
% 2.43/1.54  MUC search           : 0.00
% 2.43/1.54  Cooper               : 0.00
% 2.43/1.54  Total                : 0.68
% 2.43/1.54  Index Insertion      : 0.00
% 2.43/1.54  Index Deletion       : 0.00
% 2.43/1.54  Index Matching       : 0.00
% 2.43/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
