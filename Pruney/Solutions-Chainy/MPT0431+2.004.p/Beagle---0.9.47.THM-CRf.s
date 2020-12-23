%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:13 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   54 (  77 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 156 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v3_setfam_1(B,A)
              & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A))) )
           => ! [C] :
                ( ( v3_setfam_1(C,A)
                  & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A))) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(A),B,C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_54,plain,(
    v3_setfam_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_138,plain,(
    ! [A_57,B_58] :
      ( ~ r2_hidden(A_57,B_58)
      | ~ v3_setfam_1(B_58,A_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_141,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_setfam_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_138])).

tff(c_147,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_141])).

tff(c_50,plain,(
    v3_setfam_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_144,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ v3_setfam_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_138])).

tff(c_150,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_144])).

tff(c_188,plain,(
    ! [A_74,B_75,C_76] :
      ( k4_subset_1(A_74,B_75,C_76) = k2_xboole_0(B_75,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_74))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_226,plain,(
    ! [B_84] :
      ( k4_subset_1(k1_zfmisc_1('#skF_3'),B_84,'#skF_5') = k2_xboole_0(B_84,'#skF_5')
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_48,c_188])).

tff(c_233,plain,(
    k4_subset_1(k1_zfmisc_1('#skF_3'),'#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_226])).

tff(c_46,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1('#skF_3'),'#skF_4','#skF_5'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_235,plain,(
    ~ v3_setfam_1(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_46])).

tff(c_240,plain,(
    ! [A_85,B_86,C_87] :
      ( m1_subset_1(k4_subset_1(A_85,B_86,C_87),k1_zfmisc_1(A_85))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(A_85))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_261,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_240])).

tff(c_274,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_261])).

tff(c_42,plain,(
    ! [B_23,A_22] :
      ( v3_setfam_1(B_23,A_22)
      | r2_hidden(A_22,B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_292,plain,
    ( v3_setfam_1(k2_xboole_0('#skF_4','#skF_5'),'#skF_3')
    | r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_274,c_42])).

tff(c_299,plain,(
    r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_292])).

tff(c_32,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_117,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden(A_51,B_52)
      | r2_hidden(A_51,C_53)
      | ~ r2_hidden(A_51,k5_xboole_0(B_52,C_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_157,plain,(
    ! [A_65,A_66,B_67] :
      ( r2_hidden(A_65,A_66)
      | r2_hidden(A_65,k4_xboole_0(B_67,A_66))
      | ~ r2_hidden(A_65,k2_xboole_0(A_66,B_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_117])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_168,plain,(
    ! [A_65,B_67,A_66] :
      ( r2_hidden(A_65,B_67)
      | r2_hidden(A_65,A_66)
      | ~ r2_hidden(A_65,k2_xboole_0(A_66,B_67)) ) ),
    inference(resolution,[status(thm)],[c_157,c_6])).

tff(c_302,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_299,c_168])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_150,c_302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:02:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.34  
% 2.25/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.34  %$ v3_setfam_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.25/1.34  
% 2.25/1.34  %Foreground sorts:
% 2.25/1.34  
% 2.25/1.34  
% 2.25/1.34  %Background operators:
% 2.25/1.34  
% 2.25/1.34  
% 2.25/1.34  %Foreground operators:
% 2.25/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.25/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.25/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.25/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.34  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.25/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.25/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.25/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.25/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.25/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.34  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 2.25/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.25/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.25/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.34  
% 2.42/1.35  tff(f_83, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((v3_setfam_1(B, A) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A)))) => (![C]: ((v3_setfam_1(C, A) & m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A)))) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(A), B, C), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_setfam_1)).
% 2.42/1.35  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_setfam_1)).
% 2.42/1.35  tff(f_60, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.42/1.35  tff(f_54, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 2.42/1.35  tff(f_44, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.42/1.35  tff(f_42, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.42/1.35  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.42/1.35  tff(c_54, plain, (v3_setfam_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.42/1.35  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.42/1.35  tff(c_138, plain, (![A_57, B_58]: (~r2_hidden(A_57, B_58) | ~v3_setfam_1(B_58, A_57) | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.42/1.35  tff(c_141, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v3_setfam_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_138])).
% 2.42/1.35  tff(c_147, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_141])).
% 2.42/1.35  tff(c_50, plain, (v3_setfam_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.42/1.35  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.42/1.35  tff(c_144, plain, (~r2_hidden('#skF_3', '#skF_5') | ~v3_setfam_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_138])).
% 2.42/1.35  tff(c_150, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_144])).
% 2.42/1.35  tff(c_188, plain, (![A_74, B_75, C_76]: (k4_subset_1(A_74, B_75, C_76)=k2_xboole_0(B_75, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(A_74)) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.42/1.35  tff(c_226, plain, (![B_84]: (k4_subset_1(k1_zfmisc_1('#skF_3'), B_84, '#skF_5')=k2_xboole_0(B_84, '#skF_5') | ~m1_subset_1(B_84, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(resolution, [status(thm)], [c_48, c_188])).
% 2.42/1.35  tff(c_233, plain, (k4_subset_1(k1_zfmisc_1('#skF_3'), '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_226])).
% 2.42/1.35  tff(c_46, plain, (~v3_setfam_1(k4_subset_1(k1_zfmisc_1('#skF_3'), '#skF_4', '#skF_5'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.42/1.35  tff(c_235, plain, (~v3_setfam_1(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_233, c_46])).
% 2.42/1.35  tff(c_240, plain, (![A_85, B_86, C_87]: (m1_subset_1(k4_subset_1(A_85, B_86, C_87), k1_zfmisc_1(A_85)) | ~m1_subset_1(C_87, k1_zfmisc_1(A_85)) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.42/1.35  tff(c_261, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_233, c_240])).
% 2.42/1.35  tff(c_274, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_261])).
% 2.42/1.35  tff(c_42, plain, (![B_23, A_22]: (v3_setfam_1(B_23, A_22) | r2_hidden(A_22, B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(k1_zfmisc_1(A_22))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.42/1.35  tff(c_292, plain, (v3_setfam_1(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3') | r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_274, c_42])).
% 2.42/1.35  tff(c_299, plain, (r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_235, c_292])).
% 2.42/1.35  tff(c_32, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.42/1.35  tff(c_117, plain, (![A_51, B_52, C_53]: (r2_hidden(A_51, B_52) | r2_hidden(A_51, C_53) | ~r2_hidden(A_51, k5_xboole_0(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.42/1.35  tff(c_157, plain, (![A_65, A_66, B_67]: (r2_hidden(A_65, A_66) | r2_hidden(A_65, k4_xboole_0(B_67, A_66)) | ~r2_hidden(A_65, k2_xboole_0(A_66, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_117])).
% 2.42/1.35  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.42/1.35  tff(c_168, plain, (![A_65, B_67, A_66]: (r2_hidden(A_65, B_67) | r2_hidden(A_65, A_66) | ~r2_hidden(A_65, k2_xboole_0(A_66, B_67)))), inference(resolution, [status(thm)], [c_157, c_6])).
% 2.42/1.35  tff(c_302, plain, (r2_hidden('#skF_3', '#skF_5') | r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_299, c_168])).
% 2.42/1.35  tff(c_306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_150, c_302])).
% 2.42/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.35  
% 2.42/1.35  Inference rules
% 2.42/1.35  ----------------------
% 2.42/1.35  #Ref     : 0
% 2.42/1.35  #Sup     : 57
% 2.42/1.35  #Fact    : 0
% 2.42/1.35  #Define  : 0
% 2.42/1.35  #Split   : 0
% 2.42/1.35  #Chain   : 0
% 2.42/1.35  #Close   : 0
% 2.42/1.35  
% 2.42/1.35  Ordering : KBO
% 2.42/1.35  
% 2.42/1.35  Simplification rules
% 2.42/1.35  ----------------------
% 2.42/1.35  #Subsume      : 3
% 2.42/1.35  #Demod        : 11
% 2.42/1.35  #Tautology    : 29
% 2.42/1.35  #SimpNegUnit  : 2
% 2.42/1.35  #BackRed      : 1
% 2.42/1.35  
% 2.42/1.35  #Partial instantiations: 0
% 2.42/1.35  #Strategies tried      : 1
% 2.42/1.35  
% 2.42/1.35  Timing (in seconds)
% 2.42/1.35  ----------------------
% 2.42/1.36  Preprocessing        : 0.29
% 2.42/1.36  Parsing              : 0.15
% 2.42/1.36  CNF conversion       : 0.02
% 2.42/1.36  Main loop            : 0.22
% 2.42/1.36  Inferencing          : 0.08
% 2.42/1.36  Reduction            : 0.06
% 2.42/1.36  Demodulation         : 0.04
% 2.42/1.36  BG Simplification    : 0.02
% 2.42/1.36  Subsumption          : 0.04
% 2.42/1.36  Abstraction          : 0.01
% 2.42/1.36  MUC search           : 0.00
% 2.42/1.36  Cooper               : 0.00
% 2.42/1.36  Total                : 0.54
% 2.42/1.36  Index Insertion      : 0.00
% 2.42/1.36  Index Deletion       : 0.00
% 2.42/1.36  Index Matching       : 0.00
% 2.42/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
