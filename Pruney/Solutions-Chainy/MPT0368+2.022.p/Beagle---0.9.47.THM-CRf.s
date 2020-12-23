%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:50 EST 2020

% Result     : Theorem 6.30s
% Output     : CNFRefutation 6.66s
% Verified   : 
% Statistics : Number of formulae       :   46 (  71 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   88 ( 159 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_53,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(c_20,plain,(
    ! [A_8] : m1_subset_1('#skF_3'(A_8),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [C_15] :
      ( r2_hidden(C_15,'#skF_5')
      | ~ m1_subset_1(C_15,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_74,plain,(
    ! [C_30,A_31,B_32] :
      ( r2_hidden(C_30,A_31)
      | ~ r2_hidden(C_30,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_92,plain,(
    ! [C_35,A_36] :
      ( r2_hidden(C_35,A_36)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_36))
      | ~ m1_subset_1(C_35,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_74])).

tff(c_100,plain,(
    ! [C_37] :
      ( r2_hidden(C_37,'#skF_4')
      | ~ m1_subset_1(C_37,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_92])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( ~ v1_xboole_0(B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_116,plain,(
    ! [C_37] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_37,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_100,c_10])).

tff(c_117,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_155,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_1'(A_43,B_44),B_44)
      | r2_hidden('#skF_2'(A_43,B_44),A_43)
      | B_44 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [C_13,A_10,B_11] :
      ( r2_hidden(C_13,A_10)
      | ~ r2_hidden(C_13,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3229,plain,(
    ! [A_196,B_197,A_198] :
      ( r2_hidden('#skF_2'(A_196,B_197),A_198)
      | ~ m1_subset_1(A_196,k1_zfmisc_1(A_198))
      | r2_hidden('#skF_1'(A_196,B_197),B_197)
      | B_197 = A_196 ) ),
    inference(resolution,[status(thm)],[c_155,c_22])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3281,plain,(
    ! [A_199,A_200] :
      ( ~ m1_subset_1(A_199,k1_zfmisc_1(A_200))
      | r2_hidden('#skF_1'(A_199,A_200),A_200)
      | A_200 = A_199 ) ),
    inference(resolution,[status(thm)],[c_3229,c_4])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( m1_subset_1(B_7,A_6)
      | ~ r2_hidden(B_7,A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_7278,plain,(
    ! [A_277,A_278] :
      ( m1_subset_1('#skF_1'(A_277,A_278),A_278)
      | v1_xboole_0(A_278)
      | ~ m1_subset_1(A_277,k1_zfmisc_1(A_278))
      | A_278 = A_277 ) ),
    inference(resolution,[status(thm)],[c_3281,c_12])).

tff(c_203,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden('#skF_1'(A_47,B_48),A_47)
      | r2_hidden('#skF_2'(A_47,B_48),A_47)
      | B_48 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4404,plain,(
    ! [A_222,B_223,A_224] :
      ( r2_hidden('#skF_2'(A_222,B_223),A_224)
      | ~ m1_subset_1(A_222,k1_zfmisc_1(A_224))
      | ~ r2_hidden('#skF_1'(A_222,B_223),A_222)
      | B_223 = A_222 ) ),
    inference(resolution,[status(thm)],[c_203,c_22])).

tff(c_4521,plain,(
    ! [B_225,A_226] :
      ( r2_hidden('#skF_2'('#skF_5',B_225),A_226)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_226))
      | B_225 = '#skF_5'
      | ~ m1_subset_1('#skF_1'('#skF_5',B_225),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_4404])).

tff(c_137,plain,(
    ! [A_41,B_42] :
      ( ~ r2_hidden('#skF_1'(A_41,B_42),A_41)
      | ~ r2_hidden('#skF_2'(A_41,B_42),B_42)
      | B_42 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_154,plain,(
    ! [B_42] :
      ( ~ r2_hidden('#skF_2'('#skF_5',B_42),B_42)
      | B_42 = '#skF_5'
      | ~ m1_subset_1('#skF_1'('#skF_5',B_42),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_137])).

tff(c_4544,plain,(
    ! [A_226] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_226))
      | A_226 = '#skF_5'
      | ~ m1_subset_1('#skF_1'('#skF_5',A_226),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4521,c_154])).

tff(c_7301,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4'))
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7278,c_4544])).

tff(c_7343,plain,
    ( v1_xboole_0('#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7301])).

tff(c_7345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_117,c_7343])).

tff(c_7362,plain,(
    ! [C_280] : ~ m1_subset_1(C_280,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_7374,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_20,c_7362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:55:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.30/2.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.30/2.30  
% 6.30/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.30/2.30  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 6.30/2.30  
% 6.30/2.30  %Foreground sorts:
% 6.30/2.30  
% 6.30/2.30  
% 6.30/2.30  %Background operators:
% 6.30/2.30  
% 6.30/2.30  
% 6.30/2.30  %Foreground operators:
% 6.30/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.30/2.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.30/2.30  tff('#skF_5', type, '#skF_5': $i).
% 6.30/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.30/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.30/2.30  tff('#skF_4', type, '#skF_4': $i).
% 6.30/2.30  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.30/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.30/2.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.30/2.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.30/2.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.30/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.30/2.30  
% 6.66/2.31  tff(f_53, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 6.66/2.31  tff(f_70, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 6.66/2.31  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 6.66/2.31  tff(f_37, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 6.66/2.31  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 6.66/2.31  tff(f_50, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.66/2.31  tff(c_20, plain, (![A_8]: (m1_subset_1('#skF_3'(A_8), A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.66/2.31  tff(c_24, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.66/2.31  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.66/2.31  tff(c_26, plain, (![C_15]: (r2_hidden(C_15, '#skF_5') | ~m1_subset_1(C_15, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.66/2.31  tff(c_74, plain, (![C_30, A_31, B_32]: (r2_hidden(C_30, A_31) | ~r2_hidden(C_30, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.66/2.31  tff(c_92, plain, (![C_35, A_36]: (r2_hidden(C_35, A_36) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_36)) | ~m1_subset_1(C_35, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_74])).
% 6.66/2.31  tff(c_100, plain, (![C_37]: (r2_hidden(C_37, '#skF_4') | ~m1_subset_1(C_37, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_92])).
% 6.66/2.31  tff(c_10, plain, (![B_5, A_4]: (~v1_xboole_0(B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.66/2.31  tff(c_116, plain, (![C_37]: (~v1_xboole_0('#skF_4') | ~m1_subset_1(C_37, '#skF_4'))), inference(resolution, [status(thm)], [c_100, c_10])).
% 6.66/2.31  tff(c_117, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_116])).
% 6.66/2.31  tff(c_155, plain, (![A_43, B_44]: (r2_hidden('#skF_1'(A_43, B_44), B_44) | r2_hidden('#skF_2'(A_43, B_44), A_43) | B_44=A_43)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.31  tff(c_22, plain, (![C_13, A_10, B_11]: (r2_hidden(C_13, A_10) | ~r2_hidden(C_13, B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.66/2.31  tff(c_3229, plain, (![A_196, B_197, A_198]: (r2_hidden('#skF_2'(A_196, B_197), A_198) | ~m1_subset_1(A_196, k1_zfmisc_1(A_198)) | r2_hidden('#skF_1'(A_196, B_197), B_197) | B_197=A_196)), inference(resolution, [status(thm)], [c_155, c_22])).
% 6.66/2.31  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.31  tff(c_3281, plain, (![A_199, A_200]: (~m1_subset_1(A_199, k1_zfmisc_1(A_200)) | r2_hidden('#skF_1'(A_199, A_200), A_200) | A_200=A_199)), inference(resolution, [status(thm)], [c_3229, c_4])).
% 6.66/2.31  tff(c_12, plain, (![B_7, A_6]: (m1_subset_1(B_7, A_6) | ~r2_hidden(B_7, A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.66/2.31  tff(c_7278, plain, (![A_277, A_278]: (m1_subset_1('#skF_1'(A_277, A_278), A_278) | v1_xboole_0(A_278) | ~m1_subset_1(A_277, k1_zfmisc_1(A_278)) | A_278=A_277)), inference(resolution, [status(thm)], [c_3281, c_12])).
% 6.66/2.31  tff(c_203, plain, (![A_47, B_48]: (~r2_hidden('#skF_1'(A_47, B_48), A_47) | r2_hidden('#skF_2'(A_47, B_48), A_47) | B_48=A_47)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.31  tff(c_4404, plain, (![A_222, B_223, A_224]: (r2_hidden('#skF_2'(A_222, B_223), A_224) | ~m1_subset_1(A_222, k1_zfmisc_1(A_224)) | ~r2_hidden('#skF_1'(A_222, B_223), A_222) | B_223=A_222)), inference(resolution, [status(thm)], [c_203, c_22])).
% 6.66/2.31  tff(c_4521, plain, (![B_225, A_226]: (r2_hidden('#skF_2'('#skF_5', B_225), A_226) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_226)) | B_225='#skF_5' | ~m1_subset_1('#skF_1'('#skF_5', B_225), '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_4404])).
% 6.66/2.31  tff(c_137, plain, (![A_41, B_42]: (~r2_hidden('#skF_1'(A_41, B_42), A_41) | ~r2_hidden('#skF_2'(A_41, B_42), B_42) | B_42=A_41)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.31  tff(c_154, plain, (![B_42]: (~r2_hidden('#skF_2'('#skF_5', B_42), B_42) | B_42='#skF_5' | ~m1_subset_1('#skF_1'('#skF_5', B_42), '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_137])).
% 6.66/2.31  tff(c_4544, plain, (![A_226]: (~m1_subset_1('#skF_5', k1_zfmisc_1(A_226)) | A_226='#skF_5' | ~m1_subset_1('#skF_1'('#skF_5', A_226), '#skF_4'))), inference(resolution, [status(thm)], [c_4521, c_154])).
% 6.66/2.31  tff(c_7301, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4')) | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_7278, c_4544])).
% 6.66/2.31  tff(c_7343, plain, (v1_xboole_0('#skF_4') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7301])).
% 6.66/2.31  tff(c_7345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_117, c_7343])).
% 6.66/2.31  tff(c_7362, plain, (![C_280]: (~m1_subset_1(C_280, '#skF_4'))), inference(splitRight, [status(thm)], [c_116])).
% 6.66/2.31  tff(c_7374, plain, $false, inference(resolution, [status(thm)], [c_20, c_7362])).
% 6.66/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.31  
% 6.66/2.31  Inference rules
% 6.66/2.31  ----------------------
% 6.66/2.31  #Ref     : 0
% 6.66/2.31  #Sup     : 2084
% 6.66/2.31  #Fact    : 0
% 6.66/2.31  #Define  : 0
% 6.66/2.31  #Split   : 9
% 6.66/2.31  #Chain   : 0
% 6.66/2.31  #Close   : 0
% 6.66/2.31  
% 6.66/2.31  Ordering : KBO
% 6.66/2.31  
% 6.66/2.31  Simplification rules
% 6.66/2.31  ----------------------
% 6.66/2.31  #Subsume      : 1660
% 6.66/2.31  #Demod        : 9
% 6.66/2.31  #Tautology    : 68
% 6.66/2.31  #SimpNegUnit  : 92
% 6.66/2.31  #BackRed      : 5
% 6.66/2.31  
% 6.66/2.31  #Partial instantiations: 0
% 6.66/2.31  #Strategies tried      : 1
% 6.66/2.31  
% 6.66/2.31  Timing (in seconds)
% 6.66/2.31  ----------------------
% 6.66/2.32  Preprocessing        : 0.27
% 6.66/2.32  Parsing              : 0.14
% 6.66/2.32  CNF conversion       : 0.02
% 6.66/2.32  Main loop            : 1.29
% 6.66/2.32  Inferencing          : 0.45
% 6.66/2.32  Reduction            : 0.29
% 6.66/2.32  Demodulation         : 0.17
% 6.66/2.32  BG Simplification    : 0.03
% 6.66/2.32  Subsumption          : 0.45
% 6.66/2.32  Abstraction          : 0.06
% 6.66/2.32  MUC search           : 0.00
% 6.66/2.32  Cooper               : 0.00
% 6.66/2.32  Total                : 1.59
% 6.66/2.32  Index Insertion      : 0.00
% 6.66/2.32  Index Deletion       : 0.00
% 6.66/2.32  Index Matching       : 0.00
% 6.66/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
