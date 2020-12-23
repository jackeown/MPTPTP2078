%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:11 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   50 (  72 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   79 ( 148 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ( v3_setfam_1(B,A)
                & r1_tarski(C,B) )
             => v3_setfam_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_setfam_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_30,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_30,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_77,plain,(
    ! [B_32,A_33] :
      ( v1_xboole_0(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_104,plain,(
    ! [A_36,B_37] :
      ( v1_xboole_0(A_36)
      | ~ v1_xboole_0(B_37)
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_24,c_77])).

tff(c_116,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_104])).

tff(c_117,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r2_hidden(B_4,A_3)
      | ~ m1_subset_1(B_4,A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    v3_setfam_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_183,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden(A_46,B_47)
      | ~ v3_setfam_1(B_47,A_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_194,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | ~ v3_setfam_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_183])).

tff(c_202,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_194])).

tff(c_206,plain,
    ( ~ m1_subset_1('#skF_1','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_202])).

tff(c_209,plain,(
    ~ m1_subset_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_206])).

tff(c_28,plain,(
    ~ v3_setfam_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_285,plain,(
    ! [B_60,A_61] :
      ( v3_setfam_1(B_60,A_61)
      | r2_hidden(A_61,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(A_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_299,plain,
    ( v3_setfam_1('#skF_3','#skF_1')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_285])).

tff(c_307,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_299])).

tff(c_118,plain,(
    ! [A_38,C_39,B_40] :
      ( m1_subset_1(A_38,C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_128,plain,(
    ! [A_38,B_14,A_13] :
      ( m1_subset_1(A_38,B_14)
      | ~ r2_hidden(A_38,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_24,c_118])).

tff(c_352,plain,(
    ! [B_64] :
      ( m1_subset_1('#skF_1',B_64)
      | ~ r1_tarski('#skF_3',B_64) ) ),
    inference(resolution,[status(thm)],[c_307,c_128])).

tff(c_366,plain,(
    m1_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_352])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_366])).

tff(c_374,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_476,plain,(
    ! [B_81,A_82] :
      ( v3_setfam_1(B_81,A_82)
      | r2_hidden(A_82,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k1_zfmisc_1(A_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_490,plain,
    ( v3_setfam_1('#skF_3','#skF_1')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_476])).

tff(c_498,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_490])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_513,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_498,c_2])).

tff(c_522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:16:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.27  
% 2.19/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.27  %$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.19/1.27  
% 2.19/1.27  %Foreground sorts:
% 2.19/1.27  
% 2.19/1.27  
% 2.19/1.27  %Background operators:
% 2.19/1.27  
% 2.19/1.27  
% 2.19/1.27  %Foreground operators:
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.27  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 2.19/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.27  
% 2.19/1.28  tff(f_86, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((v3_setfam_1(B, A) & r1_tarski(C, B)) => v3_setfam_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_setfam_1)).
% 2.19/1.28  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.19/1.28  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.19/1.28  tff(f_43, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.19/1.28  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_setfam_1)).
% 2.19/1.28  tff(f_74, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.19/1.28  tff(f_30, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 2.19/1.28  tff(c_30, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.19/1.28  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.19/1.28  tff(c_77, plain, (![B_32, A_33]: (v1_xboole_0(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.19/1.28  tff(c_104, plain, (![A_36, B_37]: (v1_xboole_0(A_36) | ~v1_xboole_0(B_37) | ~r1_tarski(A_36, B_37))), inference(resolution, [status(thm)], [c_24, c_77])).
% 2.19/1.28  tff(c_116, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_104])).
% 2.19/1.28  tff(c_117, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_116])).
% 2.19/1.28  tff(c_6, plain, (![B_4, A_3]: (r2_hidden(B_4, A_3) | ~m1_subset_1(B_4, A_3) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.19/1.28  tff(c_32, plain, (v3_setfam_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.19/1.28  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.19/1.28  tff(c_183, plain, (![A_46, B_47]: (~r2_hidden(A_46, B_47) | ~v3_setfam_1(B_47, A_46) | ~m1_subset_1(B_47, k1_zfmisc_1(k1_zfmisc_1(A_46))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.19/1.28  tff(c_194, plain, (~r2_hidden('#skF_1', '#skF_2') | ~v3_setfam_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_183])).
% 2.19/1.28  tff(c_202, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_194])).
% 2.19/1.28  tff(c_206, plain, (~m1_subset_1('#skF_1', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_6, c_202])).
% 2.19/1.28  tff(c_209, plain, (~m1_subset_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_117, c_206])).
% 2.19/1.28  tff(c_28, plain, (~v3_setfam_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.19/1.28  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.19/1.28  tff(c_285, plain, (![B_60, A_61]: (v3_setfam_1(B_60, A_61) | r2_hidden(A_61, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(A_61))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.19/1.28  tff(c_299, plain, (v3_setfam_1('#skF_3', '#skF_1') | r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_285])).
% 2.19/1.28  tff(c_307, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_299])).
% 2.19/1.28  tff(c_118, plain, (![A_38, C_39, B_40]: (m1_subset_1(A_38, C_39) | ~m1_subset_1(B_40, k1_zfmisc_1(C_39)) | ~r2_hidden(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.19/1.28  tff(c_128, plain, (![A_38, B_14, A_13]: (m1_subset_1(A_38, B_14) | ~r2_hidden(A_38, A_13) | ~r1_tarski(A_13, B_14))), inference(resolution, [status(thm)], [c_24, c_118])).
% 2.19/1.28  tff(c_352, plain, (![B_64]: (m1_subset_1('#skF_1', B_64) | ~r1_tarski('#skF_3', B_64))), inference(resolution, [status(thm)], [c_307, c_128])).
% 2.19/1.28  tff(c_366, plain, (m1_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_352])).
% 2.19/1.28  tff(c_373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_366])).
% 2.19/1.28  tff(c_374, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_116])).
% 2.19/1.28  tff(c_476, plain, (![B_81, A_82]: (v3_setfam_1(B_81, A_82) | r2_hidden(A_82, B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(k1_zfmisc_1(A_82))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.19/1.28  tff(c_490, plain, (v3_setfam_1('#skF_3', '#skF_1') | r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_476])).
% 2.19/1.28  tff(c_498, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_490])).
% 2.19/1.28  tff(c_2, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.19/1.28  tff(c_513, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_498, c_2])).
% 2.19/1.28  tff(c_522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_374, c_513])).
% 2.19/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.28  
% 2.19/1.28  Inference rules
% 2.19/1.28  ----------------------
% 2.19/1.28  #Ref     : 0
% 2.19/1.28  #Sup     : 101
% 2.19/1.28  #Fact    : 0
% 2.19/1.28  #Define  : 0
% 2.19/1.28  #Split   : 6
% 2.19/1.28  #Chain   : 0
% 2.19/1.28  #Close   : 0
% 2.19/1.28  
% 2.19/1.28  Ordering : KBO
% 2.19/1.28  
% 2.19/1.28  Simplification rules
% 2.19/1.28  ----------------------
% 2.19/1.28  #Subsume      : 33
% 2.19/1.28  #Demod        : 13
% 2.19/1.28  #Tautology    : 12
% 2.19/1.28  #SimpNegUnit  : 13
% 2.19/1.28  #BackRed      : 0
% 2.19/1.28  
% 2.19/1.28  #Partial instantiations: 0
% 2.19/1.28  #Strategies tried      : 1
% 2.19/1.28  
% 2.19/1.28  Timing (in seconds)
% 2.19/1.28  ----------------------
% 2.19/1.29  Preprocessing        : 0.26
% 2.19/1.29  Parsing              : 0.14
% 2.19/1.29  CNF conversion       : 0.02
% 2.19/1.29  Main loop            : 0.27
% 2.19/1.29  Inferencing          : 0.11
% 2.19/1.29  Reduction            : 0.07
% 2.19/1.29  Demodulation         : 0.04
% 2.19/1.29  BG Simplification    : 0.01
% 2.19/1.29  Subsumption          : 0.05
% 2.19/1.29  Abstraction          : 0.01
% 2.19/1.29  MUC search           : 0.00
% 2.19/1.29  Cooper               : 0.00
% 2.19/1.29  Total                : 0.57
% 2.19/1.29  Index Insertion      : 0.00
% 2.19/1.29  Index Deletion       : 0.00
% 2.19/1.29  Index Matching       : 0.00
% 2.19/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
