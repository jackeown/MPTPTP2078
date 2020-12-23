%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:50 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 112 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 239 expanded)
%              Number of equality atoms :   11 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_70,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_54,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_30,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [A_15] : ~ v1_xboole_0(k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_160,plain,(
    ! [B_49,A_50] :
      ( r2_hidden(B_49,A_50)
      | ~ m1_subset_1(B_49,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [A_12] : k3_tarski(k1_zfmisc_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_59,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,k3_tarski(B_28))
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_62,plain,(
    ! [A_27,A_12] :
      ( r1_tarski(A_27,A_12)
      | ~ r2_hidden(A_27,k1_zfmisc_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_59])).

tff(c_168,plain,(
    ! [B_49,A_12] :
      ( r1_tarski(B_49,A_12)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_160,c_62])).

tff(c_278,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(B_61,A_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_168])).

tff(c_298,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_278])).

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

tff(c_177,plain,(
    ! [B_51,A_52] :
      ( m1_subset_1(B_51,A_52)
      | ~ r2_hidden(B_51,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_198,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_177])).

tff(c_48,plain,(
    ! [C_25] :
      ( r2_hidden(C_25,'#skF_4')
      | ~ m1_subset_1(C_25,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [C_25] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_25,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_53,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_32,plain,(
    ! [C_17] :
      ( r2_hidden(C_17,'#skF_4')
      | ~ m1_subset_1(C_17,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_192,plain,(
    ! [C_17] :
      ( m1_subset_1(C_17,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_17,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_177])).

tff(c_211,plain,(
    ! [C_54] :
      ( m1_subset_1(C_54,'#skF_4')
      | ~ m1_subset_1(C_54,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_192])).

tff(c_220,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_198,c_211])).

tff(c_222,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_233,plain,(
    ! [B_57,A_58] :
      ( r1_tarski(B_57,A_58)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_168])).

tff(c_253,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_233])).

tff(c_94,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_2'(A_38,B_39),B_39)
      | ~ r2_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_104,plain,(
    ! [B_40,A_41] :
      ( ~ v1_xboole_0(B_40)
      | ~ r2_xboole_0(A_41,B_40) ) ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_108,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_256,plain,
    ( ~ v1_xboole_0('#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_253,c_108])).

tff(c_259,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_256])).

tff(c_261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_259])).

tff(c_263,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),B_8)
      | ~ r2_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_308,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1('#skF_2'(A_65,B_66),B_66)
      | v1_xboole_0(B_66)
      | ~ r2_xboole_0(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_14,c_177])).

tff(c_109,plain,(
    ! [A_42,B_43] :
      ( ~ r2_hidden('#skF_2'(A_42,B_43),A_42)
      | ~ r2_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_119,plain,(
    ! [B_43] :
      ( ~ r2_xboole_0('#skF_4',B_43)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_43),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_109])).

tff(c_316,plain,
    ( v1_xboole_0('#skF_3')
    | ~ r2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_308,c_119])).

tff(c_329,plain,(
    ~ r2_xboole_0('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_316])).

tff(c_336,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_329])).

tff(c_339,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_336])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.67  
% 2.48/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.67  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.48/1.67  
% 2.48/1.67  %Foreground sorts:
% 2.48/1.67  
% 2.48/1.67  
% 2.48/1.67  %Background operators:
% 2.48/1.67  
% 2.48/1.67  
% 2.48/1.67  %Foreground operators:
% 2.48/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.48/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.67  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.67  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.48/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.48/1.67  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.48/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.48/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.48/1.67  
% 2.48/1.70  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 2.48/1.70  tff(f_70, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.48/1.70  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.48/1.70  tff(f_54, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.48/1.70  tff(f_52, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.48/1.70  tff(f_38, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.48/1.70  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.48/1.70  tff(f_48, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.48/1.70  tff(c_30, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.48/1.70  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.48/1.70  tff(c_28, plain, (![A_15]: (~v1_xboole_0(k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.48/1.70  tff(c_160, plain, (![B_49, A_50]: (r2_hidden(B_49, A_50) | ~m1_subset_1(B_49, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.48/1.70  tff(c_18, plain, (![A_12]: (k3_tarski(k1_zfmisc_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.48/1.70  tff(c_59, plain, (![A_27, B_28]: (r1_tarski(A_27, k3_tarski(B_28)) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.48/1.70  tff(c_62, plain, (![A_27, A_12]: (r1_tarski(A_27, A_12) | ~r2_hidden(A_27, k1_zfmisc_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_59])).
% 2.48/1.70  tff(c_168, plain, (![B_49, A_12]: (r1_tarski(B_49, A_12) | ~m1_subset_1(B_49, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)))), inference(resolution, [status(thm)], [c_160, c_62])).
% 2.48/1.70  tff(c_278, plain, (![B_61, A_62]: (r1_tarski(B_61, A_62) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)))), inference(negUnitSimplification, [status(thm)], [c_28, c_168])).
% 2.48/1.70  tff(c_298, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_278])).
% 2.48/1.70  tff(c_6, plain, (![A_5, B_6]: (r2_xboole_0(A_5, B_6) | B_6=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.70  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.70  tff(c_177, plain, (![B_51, A_52]: (m1_subset_1(B_51, A_52) | ~r2_hidden(B_51, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.48/1.70  tff(c_198, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_177])).
% 2.48/1.70  tff(c_48, plain, (![C_25]: (r2_hidden(C_25, '#skF_4') | ~m1_subset_1(C_25, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.48/1.70  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.70  tff(c_52, plain, (![C_25]: (~v1_xboole_0('#skF_4') | ~m1_subset_1(C_25, '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_2])).
% 2.48/1.70  tff(c_53, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 2.48/1.70  tff(c_32, plain, (![C_17]: (r2_hidden(C_17, '#skF_4') | ~m1_subset_1(C_17, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.48/1.70  tff(c_192, plain, (![C_17]: (m1_subset_1(C_17, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(C_17, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_177])).
% 2.48/1.70  tff(c_211, plain, (![C_54]: (m1_subset_1(C_54, '#skF_4') | ~m1_subset_1(C_54, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_53, c_192])).
% 2.48/1.70  tff(c_220, plain, (m1_subset_1('#skF_1'('#skF_3'), '#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_198, c_211])).
% 2.48/1.70  tff(c_222, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_220])).
% 2.48/1.70  tff(c_233, plain, (![B_57, A_58]: (r1_tarski(B_57, A_58) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)))), inference(negUnitSimplification, [status(thm)], [c_28, c_168])).
% 2.48/1.70  tff(c_253, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_233])).
% 2.48/1.70  tff(c_94, plain, (![A_38, B_39]: (r2_hidden('#skF_2'(A_38, B_39), B_39) | ~r2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.48/1.70  tff(c_104, plain, (![B_40, A_41]: (~v1_xboole_0(B_40) | ~r2_xboole_0(A_41, B_40))), inference(resolution, [status(thm)], [c_94, c_2])).
% 2.48/1.70  tff(c_108, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_6, c_104])).
% 2.48/1.70  tff(c_256, plain, (~v1_xboole_0('#skF_3') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_253, c_108])).
% 2.48/1.70  tff(c_259, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_222, c_256])).
% 2.48/1.70  tff(c_261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_259])).
% 2.48/1.70  tff(c_263, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_220])).
% 2.48/1.70  tff(c_14, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), B_8) | ~r2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.48/1.70  tff(c_308, plain, (![A_65, B_66]: (m1_subset_1('#skF_2'(A_65, B_66), B_66) | v1_xboole_0(B_66) | ~r2_xboole_0(A_65, B_66))), inference(resolution, [status(thm)], [c_14, c_177])).
% 2.48/1.70  tff(c_109, plain, (![A_42, B_43]: (~r2_hidden('#skF_2'(A_42, B_43), A_42) | ~r2_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.48/1.70  tff(c_119, plain, (![B_43]: (~r2_xboole_0('#skF_4', B_43) | ~m1_subset_1('#skF_2'('#skF_4', B_43), '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_109])).
% 2.48/1.70  tff(c_316, plain, (v1_xboole_0('#skF_3') | ~r2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_308, c_119])).
% 2.48/1.70  tff(c_329, plain, (~r2_xboole_0('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_263, c_316])).
% 2.48/1.70  tff(c_336, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_329])).
% 2.48/1.70  tff(c_339, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_298, c_336])).
% 2.48/1.70  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_339])).
% 2.48/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.70  
% 2.48/1.70  Inference rules
% 2.48/1.70  ----------------------
% 2.48/1.70  #Ref     : 0
% 2.48/1.70  #Sup     : 57
% 2.48/1.70  #Fact    : 0
% 2.48/1.70  #Define  : 0
% 2.48/1.70  #Split   : 2
% 2.48/1.70  #Chain   : 0
% 2.48/1.70  #Close   : 0
% 2.48/1.70  
% 2.48/1.70  Ordering : KBO
% 2.48/1.70  
% 2.48/1.70  Simplification rules
% 2.48/1.70  ----------------------
% 2.48/1.70  #Subsume      : 17
% 2.48/1.70  #Demod        : 5
% 2.48/1.70  #Tautology    : 14
% 2.48/1.70  #SimpNegUnit  : 15
% 2.48/1.70  #BackRed      : 0
% 2.48/1.70  
% 2.48/1.70  #Partial instantiations: 0
% 2.48/1.70  #Strategies tried      : 1
% 2.48/1.70  
% 2.48/1.70  Timing (in seconds)
% 2.48/1.70  ----------------------
% 2.69/1.70  Preprocessing        : 0.45
% 2.69/1.70  Parsing              : 0.23
% 2.69/1.70  CNF conversion       : 0.03
% 2.69/1.70  Main loop            : 0.35
% 2.69/1.70  Inferencing          : 0.14
% 2.69/1.70  Reduction            : 0.09
% 2.69/1.70  Demodulation         : 0.05
% 2.69/1.70  BG Simplification    : 0.02
% 2.69/1.70  Subsumption          : 0.07
% 2.69/1.70  Abstraction          : 0.01
% 2.69/1.71  MUC search           : 0.00
% 2.69/1.71  Cooper               : 0.00
% 2.69/1.71  Total                : 0.86
% 2.69/1.71  Index Insertion      : 0.00
% 2.69/1.71  Index Deletion       : 0.00
% 2.69/1.71  Index Matching       : 0.00
% 2.69/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
