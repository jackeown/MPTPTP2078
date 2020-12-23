%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:11 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   53 (  75 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   77 ( 146 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ( v3_setfam_1(B,A)
                & r1_tarski(C,B) )
             => v3_setfam_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_32,plain,(
    v3_setfam_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_65,plain,(
    ! [A_34,B_35] :
      ( r2_xboole_0(A_34,B_35)
      | B_35 = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_2'(A_30,B_31),B_31)
      | ~ r2_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [B_31,A_30] :
      ( ~ v1_xboole_0(B_31)
      | ~ r2_xboole_0(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_80,plain,(
    ! [B_36,A_37] :
      ( ~ v1_xboole_0(B_36)
      | B_36 = A_37
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(resolution,[status(thm)],[c_65,c_63])).

tff(c_92,plain,
    ( ~ v1_xboole_0('#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_80])).

tff(c_93,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_121,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden(A_45,B_46)
      | ~ v3_setfam_1(B_46,A_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(A_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_128,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_setfam_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_121])).

tff(c_135,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_128])).

tff(c_139,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_135])).

tff(c_142,plain,(
    ~ m1_subset_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_139])).

tff(c_28,plain,(
    ~ v3_setfam_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_200,plain,(
    ! [B_51,A_52] :
      ( v3_setfam_1(B_51,A_52)
      | r2_hidden(A_52,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_210,plain,
    ( v3_setfam_1('#skF_5','#skF_3')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_200])).

tff(c_217,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_210])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_111,plain,(
    ! [A_42,C_43,B_44] :
      ( m1_subset_1(A_42,C_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(C_43))
      | ~ r2_hidden(A_42,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_260,plain,(
    ! [A_56,B_57,A_58] :
      ( m1_subset_1(A_56,B_57)
      | ~ r2_hidden(A_56,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(resolution,[status(thm)],[c_24,c_111])).

tff(c_273,plain,(
    ! [B_59] :
      ( m1_subset_1('#skF_3',B_59)
      | ~ r1_tarski('#skF_5',B_59) ) ),
    inference(resolution,[status(thm)],[c_217,c_260])).

tff(c_283,plain,(
    m1_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_273])).

tff(c_289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_283])).

tff(c_290,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_294,plain,(
    ~ v3_setfam_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_28])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.31  
% 2.05/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.31  %$ v3_setfam_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.05/1.31  
% 2.05/1.31  %Foreground sorts:
% 2.05/1.31  
% 2.05/1.31  
% 2.05/1.31  %Background operators:
% 2.05/1.31  
% 2.05/1.31  
% 2.05/1.31  %Foreground operators:
% 2.05/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.05/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.31  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.05/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.05/1.31  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 2.05/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.05/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.31  
% 2.05/1.33  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((v3_setfam_1(B, A) & r1_tarski(C, B)) => v3_setfam_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_setfam_1)).
% 2.05/1.33  tff(f_38, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.05/1.33  tff(f_48, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.05/1.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.05/1.33  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.05/1.33  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_setfam_1)).
% 2.05/1.33  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.05/1.33  tff(f_71, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.05/1.33  tff(c_32, plain, (v3_setfam_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.05/1.33  tff(c_30, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.05/1.33  tff(c_65, plain, (![A_34, B_35]: (r2_xboole_0(A_34, B_35) | B_35=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.05/1.33  tff(c_59, plain, (![A_30, B_31]: (r2_hidden('#skF_2'(A_30, B_31), B_31) | ~r2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.05/1.33  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.05/1.33  tff(c_63, plain, (![B_31, A_30]: (~v1_xboole_0(B_31) | ~r2_xboole_0(A_30, B_31))), inference(resolution, [status(thm)], [c_59, c_2])).
% 2.05/1.33  tff(c_80, plain, (![B_36, A_37]: (~v1_xboole_0(B_36) | B_36=A_37 | ~r1_tarski(A_37, B_36))), inference(resolution, [status(thm)], [c_65, c_63])).
% 2.05/1.33  tff(c_92, plain, (~v1_xboole_0('#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_30, c_80])).
% 2.05/1.33  tff(c_93, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_92])).
% 2.05/1.33  tff(c_20, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.05/1.33  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.05/1.33  tff(c_121, plain, (![A_45, B_46]: (~r2_hidden(A_45, B_46) | ~v3_setfam_1(B_46, A_45) | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(A_45))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.05/1.33  tff(c_128, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v3_setfam_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_121])).
% 2.05/1.33  tff(c_135, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_128])).
% 2.05/1.33  tff(c_139, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_135])).
% 2.05/1.33  tff(c_142, plain, (~m1_subset_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_93, c_139])).
% 2.05/1.33  tff(c_28, plain, (~v3_setfam_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.05/1.33  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.05/1.33  tff(c_200, plain, (![B_51, A_52]: (v3_setfam_1(B_51, A_52) | r2_hidden(A_52, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(k1_zfmisc_1(A_52))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.05/1.33  tff(c_210, plain, (v3_setfam_1('#skF_5', '#skF_3') | r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_200])).
% 2.05/1.33  tff(c_217, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_28, c_210])).
% 2.05/1.33  tff(c_24, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.05/1.33  tff(c_111, plain, (![A_42, C_43, B_44]: (m1_subset_1(A_42, C_43) | ~m1_subset_1(B_44, k1_zfmisc_1(C_43)) | ~r2_hidden(A_42, B_44))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.33  tff(c_260, plain, (![A_56, B_57, A_58]: (m1_subset_1(A_56, B_57) | ~r2_hidden(A_56, A_58) | ~r1_tarski(A_58, B_57))), inference(resolution, [status(thm)], [c_24, c_111])).
% 2.05/1.33  tff(c_273, plain, (![B_59]: (m1_subset_1('#skF_3', B_59) | ~r1_tarski('#skF_5', B_59))), inference(resolution, [status(thm)], [c_217, c_260])).
% 2.05/1.33  tff(c_283, plain, (m1_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_273])).
% 2.05/1.33  tff(c_289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_283])).
% 2.05/1.33  tff(c_290, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_92])).
% 2.05/1.33  tff(c_294, plain, (~v3_setfam_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_290, c_28])).
% 2.05/1.33  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_294])).
% 2.05/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.33  
% 2.05/1.33  Inference rules
% 2.05/1.33  ----------------------
% 2.05/1.33  #Ref     : 0
% 2.05/1.33  #Sup     : 52
% 2.05/1.33  #Fact    : 0
% 2.05/1.33  #Define  : 0
% 2.05/1.33  #Split   : 4
% 2.05/1.33  #Chain   : 0
% 2.05/1.33  #Close   : 0
% 2.05/1.33  
% 2.05/1.33  Ordering : KBO
% 2.05/1.33  
% 2.05/1.33  Simplification rules
% 2.05/1.33  ----------------------
% 2.05/1.33  #Subsume      : 6
% 2.05/1.33  #Demod        : 9
% 2.05/1.33  #Tautology    : 8
% 2.05/1.33  #SimpNegUnit  : 8
% 2.05/1.33  #BackRed      : 4
% 2.05/1.33  
% 2.05/1.33  #Partial instantiations: 0
% 2.05/1.33  #Strategies tried      : 1
% 2.05/1.33  
% 2.05/1.33  Timing (in seconds)
% 2.05/1.33  ----------------------
% 2.05/1.33  Preprocessing        : 0.29
% 2.05/1.33  Parsing              : 0.17
% 2.05/1.33  CNF conversion       : 0.02
% 2.05/1.33  Main loop            : 0.22
% 2.05/1.33  Inferencing          : 0.09
% 2.05/1.33  Reduction            : 0.06
% 2.05/1.33  Demodulation         : 0.04
% 2.05/1.33  BG Simplification    : 0.01
% 2.05/1.33  Subsumption          : 0.04
% 2.05/1.33  Abstraction          : 0.01
% 2.05/1.33  MUC search           : 0.00
% 2.05/1.33  Cooper               : 0.00
% 2.05/1.33  Total                : 0.54
% 2.05/1.33  Index Insertion      : 0.00
% 2.05/1.33  Index Deletion       : 0.00
% 2.05/1.33  Index Matching       : 0.00
% 2.05/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
