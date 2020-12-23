%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:48 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 107 expanded)
%              Number of leaves         :   21 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   94 ( 239 expanded)
%              Number of equality atoms :    6 (  23 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_66,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

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
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_40,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_162,plain,(
    ! [B_52,A_53] :
      ( r2_hidden(B_52,A_53)
      | ~ m1_subset_1(B_52,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [C_14,A_10] :
      ( r1_tarski(C_14,A_10)
      | ~ r2_hidden(C_14,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_177,plain,(
    ! [B_52,A_10] :
      ( r1_tarski(B_52,A_10)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_10))
      | v1_xboole_0(k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_162,c_16])).

tff(c_192,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(B_54,A_55)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_177])).

tff(c_205,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_192])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_207,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_205,c_10])).

tff(c_210,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_207])).

tff(c_79,plain,(
    ! [B_37,A_38] :
      ( m1_subset_1(B_37,A_38)
      | ~ v1_xboole_0(B_37)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    ! [C_23] :
      ( r2_hidden(C_23,'#skF_5')
      | ~ m1_subset_1(C_23,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_49,plain,(
    ! [B_27,A_28] :
      ( ~ r2_hidden(B_27,A_28)
      | ~ r2_hidden(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_53,plain,(
    ! [C_29] :
      ( ~ r2_hidden('#skF_5',C_29)
      | ~ m1_subset_1(C_29,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_49])).

tff(c_58,plain,(
    ~ m1_subset_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_53])).

tff(c_91,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_58])).

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_142,plain,(
    ! [B_48,A_49] :
      ( m1_subset_1(B_48,A_49)
      | ~ r2_hidden(B_48,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_650,plain,(
    ! [A_103,B_104] :
      ( m1_subset_1('#skF_1'(A_103,B_104),A_103)
      | v1_xboole_0(A_103)
      | r1_tarski(A_103,B_104) ) ),
    inference(resolution,[status(thm)],[c_8,c_142])).

tff(c_120,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden('#skF_1'(A_45,B_46),B_46)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [A_45] :
      ( r1_tarski(A_45,'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_45,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_120])).

tff(c_666,plain,
    ( v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_650,c_136])).

tff(c_680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_92,c_210,c_666])).

tff(c_682,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_32,plain,(
    ! [B_16,A_15] :
      ( m1_subset_1(B_16,A_15)
      | ~ v1_xboole_0(B_16)
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_879,plain,(
    ! [C_135,A_136,B_137] :
      ( r2_hidden(C_135,A_136)
      | ~ r2_hidden(C_135,B_137)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_953,plain,(
    ! [C_142,A_143] :
      ( r2_hidden(C_142,A_143)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_143))
      | ~ m1_subset_1(C_142,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_879])).

tff(c_964,plain,(
    ! [C_142] :
      ( r2_hidden(C_142,'#skF_4')
      | ~ m1_subset_1(C_142,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_953])).

tff(c_965,plain,(
    ! [C_144] :
      ( r2_hidden(C_144,'#skF_4')
      | ~ m1_subset_1(C_144,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_953])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_999,plain,(
    ! [C_145] :
      ( ~ r2_hidden('#skF_4',C_145)
      | ~ m1_subset_1(C_145,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_965,c_2])).

tff(c_1020,plain,(
    ~ m1_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_964,c_999])).

tff(c_1027,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1020])).

tff(c_1031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_1027])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:59:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.41  
% 2.97/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.42  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.97/1.42  
% 2.97/1.42  %Foreground sorts:
% 2.97/1.42  
% 2.97/1.42  
% 2.97/1.42  %Background operators:
% 2.97/1.42  
% 2.97/1.42  
% 2.97/1.42  %Foreground operators:
% 2.97/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.97/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.97/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.97/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.97/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.97/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.42  
% 2.97/1.43  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 2.97/1.43  tff(f_66, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.97/1.43  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.97/1.43  tff(f_50, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.97/1.43  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.97/1.43  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 2.97/1.43  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.97/1.43  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.97/1.43  tff(c_40, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.97/1.43  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.97/1.43  tff(c_36, plain, (![A_17]: (~v1_xboole_0(k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.97/1.43  tff(c_162, plain, (![B_52, A_53]: (r2_hidden(B_52, A_53) | ~m1_subset_1(B_52, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.97/1.43  tff(c_16, plain, (![C_14, A_10]: (r1_tarski(C_14, A_10) | ~r2_hidden(C_14, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.97/1.43  tff(c_177, plain, (![B_52, A_10]: (r1_tarski(B_52, A_10) | ~m1_subset_1(B_52, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_162, c_16])).
% 2.97/1.43  tff(c_192, plain, (![B_54, A_55]: (r1_tarski(B_54, A_55) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)))), inference(negUnitSimplification, [status(thm)], [c_36, c_177])).
% 2.97/1.43  tff(c_205, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_192])).
% 2.97/1.43  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.97/1.43  tff(c_207, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_205, c_10])).
% 2.97/1.43  tff(c_210, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_207])).
% 2.97/1.43  tff(c_79, plain, (![B_37, A_38]: (m1_subset_1(B_37, A_38) | ~v1_xboole_0(B_37) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.97/1.43  tff(c_42, plain, (![C_23]: (r2_hidden(C_23, '#skF_5') | ~m1_subset_1(C_23, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.97/1.43  tff(c_49, plain, (![B_27, A_28]: (~r2_hidden(B_27, A_28) | ~r2_hidden(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.97/1.43  tff(c_53, plain, (![C_29]: (~r2_hidden('#skF_5', C_29) | ~m1_subset_1(C_29, '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_49])).
% 2.97/1.43  tff(c_58, plain, (~m1_subset_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_53])).
% 2.97/1.43  tff(c_91, plain, (~v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_79, c_58])).
% 2.97/1.43  tff(c_92, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_91])).
% 2.97/1.43  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.97/1.43  tff(c_142, plain, (![B_48, A_49]: (m1_subset_1(B_48, A_49) | ~r2_hidden(B_48, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.97/1.43  tff(c_650, plain, (![A_103, B_104]: (m1_subset_1('#skF_1'(A_103, B_104), A_103) | v1_xboole_0(A_103) | r1_tarski(A_103, B_104))), inference(resolution, [status(thm)], [c_8, c_142])).
% 2.97/1.43  tff(c_120, plain, (![A_45, B_46]: (~r2_hidden('#skF_1'(A_45, B_46), B_46) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.97/1.43  tff(c_136, plain, (![A_45]: (r1_tarski(A_45, '#skF_5') | ~m1_subset_1('#skF_1'(A_45, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_120])).
% 2.97/1.43  tff(c_666, plain, (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_650, c_136])).
% 2.97/1.43  tff(c_680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_210, c_92, c_210, c_666])).
% 2.97/1.43  tff(c_682, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_91])).
% 2.97/1.43  tff(c_32, plain, (![B_16, A_15]: (m1_subset_1(B_16, A_15) | ~v1_xboole_0(B_16) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.97/1.43  tff(c_879, plain, (![C_135, A_136, B_137]: (r2_hidden(C_135, A_136) | ~r2_hidden(C_135, B_137) | ~m1_subset_1(B_137, k1_zfmisc_1(A_136)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.97/1.43  tff(c_953, plain, (![C_142, A_143]: (r2_hidden(C_142, A_143) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_143)) | ~m1_subset_1(C_142, '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_879])).
% 2.97/1.43  tff(c_964, plain, (![C_142]: (r2_hidden(C_142, '#skF_4') | ~m1_subset_1(C_142, '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_953])).
% 2.97/1.43  tff(c_965, plain, (![C_144]: (r2_hidden(C_144, '#skF_4') | ~m1_subset_1(C_144, '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_953])).
% 2.97/1.43  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.97/1.43  tff(c_999, plain, (![C_145]: (~r2_hidden('#skF_4', C_145) | ~m1_subset_1(C_145, '#skF_4'))), inference(resolution, [status(thm)], [c_965, c_2])).
% 2.97/1.43  tff(c_1020, plain, (~m1_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_964, c_999])).
% 2.97/1.43  tff(c_1027, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_32, c_1020])).
% 2.97/1.43  tff(c_1031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_682, c_1027])).
% 2.97/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.43  
% 2.97/1.43  Inference rules
% 2.97/1.43  ----------------------
% 2.97/1.43  #Ref     : 0
% 2.97/1.43  #Sup     : 210
% 2.97/1.43  #Fact    : 0
% 2.97/1.43  #Define  : 0
% 2.97/1.43  #Split   : 2
% 2.97/1.43  #Chain   : 0
% 2.97/1.43  #Close   : 0
% 2.97/1.43  
% 2.97/1.43  Ordering : KBO
% 2.97/1.43  
% 2.97/1.43  Simplification rules
% 2.97/1.43  ----------------------
% 2.97/1.43  #Subsume      : 53
% 2.97/1.43  #Demod        : 14
% 2.97/1.43  #Tautology    : 18
% 2.97/1.43  #SimpNegUnit  : 21
% 2.97/1.43  #BackRed      : 0
% 2.97/1.43  
% 2.97/1.43  #Partial instantiations: 0
% 2.97/1.43  #Strategies tried      : 1
% 2.97/1.43  
% 2.97/1.43  Timing (in seconds)
% 2.97/1.43  ----------------------
% 2.97/1.43  Preprocessing        : 0.30
% 2.97/1.43  Parsing              : 0.16
% 2.97/1.43  CNF conversion       : 0.02
% 2.97/1.43  Main loop            : 0.37
% 2.97/1.43  Inferencing          : 0.14
% 2.97/1.43  Reduction            : 0.09
% 2.97/1.43  Demodulation         : 0.06
% 2.97/1.43  BG Simplification    : 0.02
% 2.97/1.43  Subsumption          : 0.10
% 2.97/1.43  Abstraction          : 0.02
% 2.97/1.43  MUC search           : 0.00
% 2.97/1.43  Cooper               : 0.00
% 2.97/1.43  Total                : 0.70
% 2.97/1.43  Index Insertion      : 0.00
% 2.97/1.43  Index Deletion       : 0.00
% 2.97/1.43  Index Matching       : 0.00
% 2.97/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
