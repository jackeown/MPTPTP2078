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

% Result     : Theorem 14.36s
% Output     : CNFRefutation 14.36s
% Verified   : 
% Statistics : Number of formulae       :   59 (  82 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 165 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_84,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_61,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_46,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_42,plain,(
    v3_setfam_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_122,plain,(
    ! [A_55,B_56] :
      ( ~ r2_hidden(A_55,B_56)
      | ~ v3_setfam_1(B_56,A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_129,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | ~ v3_setfam_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_122])).

tff(c_136,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_129])).

tff(c_38,plain,(
    v3_setfam_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_132,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | ~ v3_setfam_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_122])).

tff(c_139,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_132])).

tff(c_201,plain,(
    ! [A_78,B_79,C_80] :
      ( k4_subset_1(A_78,B_79,C_80) = k2_xboole_0(B_79,C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(A_78))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4192,plain,(
    ! [B_219] :
      ( k4_subset_1(k1_zfmisc_1('#skF_1'),B_219,'#skF_3') = k2_xboole_0(B_219,'#skF_3')
      | ~ m1_subset_1(B_219,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_36,c_201])).

tff(c_4217,plain,(
    k4_subset_1(k1_zfmisc_1('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_4192])).

tff(c_34,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4219,plain,(
    ~ v3_setfam_1(k2_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4217,c_34])).

tff(c_20,plain,(
    ! [A_10,B_11,C_12] :
      ( m1_subset_1(k4_subset_1(A_10,B_11,C_12),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4223,plain,
    ( m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4217,c_20])).

tff(c_4227,plain,(
    m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_4223])).

tff(c_30,plain,(
    ! [B_25,A_24] :
      ( v3_setfam_1(B_25,A_24)
      | r2_hidden(A_24,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4239,plain,
    ( v3_setfam_1(k2_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | r2_hidden('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4227,c_30])).

tff(c_4248,plain,(
    r2_hidden('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_4219,c_4239])).

tff(c_28,plain,(
    ! [A_22,B_23] : k6_subset_1(A_22,B_23) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_13,B_14] : m1_subset_1(k6_subset_1(A_13,B_14),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_45,plain,(
    ! [A_13,B_14] : m1_subset_1(k4_xboole_0(A_13,B_14),k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22])).

tff(c_14,plain,(
    ! [A_4,B_5] : k5_xboole_0(A_4,k4_xboole_0(B_5,A_4)) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_91,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden(A_46,B_47)
      | r2_hidden(A_46,C_48)
      | ~ r2_hidden(A_46,k5_xboole_0(B_47,C_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_189,plain,(
    ! [A_75,A_76,B_77] :
      ( r2_hidden(A_75,A_76)
      | r2_hidden(A_75,k4_xboole_0(B_77,A_76))
      | ~ r2_hidden(A_75,k2_xboole_0(A_76,B_77)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_91])).

tff(c_24,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38292,plain,(
    ! [A_1307,A_1308,B_1309,A_1310] :
      ( r2_hidden(A_1307,A_1308)
      | ~ m1_subset_1(k4_xboole_0(B_1309,A_1310),k1_zfmisc_1(A_1308))
      | r2_hidden(A_1307,A_1310)
      | ~ r2_hidden(A_1307,k2_xboole_0(A_1310,B_1309)) ) ),
    inference(resolution,[status(thm)],[c_189,c_24])).

tff(c_38300,plain,(
    ! [A_1312,A_1313,B_1314] :
      ( r2_hidden(A_1312,A_1313)
      | r2_hidden(A_1312,B_1314)
      | ~ r2_hidden(A_1312,k2_xboole_0(B_1314,A_1313)) ) ),
    inference(resolution,[status(thm)],[c_45,c_38292])).

tff(c_38312,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4248,c_38300])).

tff(c_38323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_139,c_38312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.36/6.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.36/6.94  
% 14.36/6.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.36/6.94  %$ v3_setfam_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 14.36/6.94  
% 14.36/6.94  %Foreground sorts:
% 14.36/6.94  
% 14.36/6.94  
% 14.36/6.94  %Background operators:
% 14.36/6.94  
% 14.36/6.94  
% 14.36/6.94  %Foreground operators:
% 14.36/6.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.36/6.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.36/6.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.36/6.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.36/6.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.36/6.94  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 14.36/6.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.36/6.94  tff('#skF_2', type, '#skF_2': $i).
% 14.36/6.94  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 14.36/6.94  tff('#skF_3', type, '#skF_3': $i).
% 14.36/6.94  tff('#skF_1', type, '#skF_1': $i).
% 14.36/6.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.36/6.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.36/6.94  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.36/6.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.36/6.94  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 14.36/6.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.36/6.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.36/6.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.36/6.94  
% 14.36/6.95  tff(f_84, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((v3_setfam_1(B, A) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A)))) => (![C]: ((v3_setfam_1(C, A) & m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A)))) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(A), B, C), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_setfam_1)).
% 14.36/6.95  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_setfam_1)).
% 14.36/6.95  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 14.36/6.95  tff(f_44, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 14.36/6.95  tff(f_61, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 14.36/6.95  tff(f_46, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 14.36/6.95  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 14.36/6.95  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 14.36/6.95  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 14.36/6.95  tff(c_42, plain, (v3_setfam_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.36/6.95  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.36/6.95  tff(c_122, plain, (![A_55, B_56]: (~r2_hidden(A_55, B_56) | ~v3_setfam_1(B_56, A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.36/6.95  tff(c_129, plain, (~r2_hidden('#skF_1', '#skF_2') | ~v3_setfam_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_122])).
% 14.36/6.95  tff(c_136, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_129])).
% 14.36/6.95  tff(c_38, plain, (v3_setfam_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.36/6.95  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.36/6.95  tff(c_132, plain, (~r2_hidden('#skF_1', '#skF_3') | ~v3_setfam_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_122])).
% 14.36/6.95  tff(c_139, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_132])).
% 14.36/6.95  tff(c_201, plain, (![A_78, B_79, C_80]: (k4_subset_1(A_78, B_79, C_80)=k2_xboole_0(B_79, C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(A_78)) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.36/6.95  tff(c_4192, plain, (![B_219]: (k4_subset_1(k1_zfmisc_1('#skF_1'), B_219, '#skF_3')=k2_xboole_0(B_219, '#skF_3') | ~m1_subset_1(B_219, k1_zfmisc_1(k1_zfmisc_1('#skF_1'))))), inference(resolution, [status(thm)], [c_36, c_201])).
% 14.36/6.95  tff(c_4217, plain, (k4_subset_1(k1_zfmisc_1('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_4192])).
% 14.36/6.95  tff(c_34, plain, (~v3_setfam_1(k4_subset_1(k1_zfmisc_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.36/6.95  tff(c_4219, plain, (~v3_setfam_1(k2_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4217, c_34])).
% 14.36/6.95  tff(c_20, plain, (![A_10, B_11, C_12]: (m1_subset_1(k4_subset_1(A_10, B_11, C_12), k1_zfmisc_1(A_10)) | ~m1_subset_1(C_12, k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 14.36/6.95  tff(c_4223, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4217, c_20])).
% 14.36/6.95  tff(c_4227, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_4223])).
% 14.36/6.95  tff(c_30, plain, (![B_25, A_24]: (v3_setfam_1(B_25, A_24) | r2_hidden(A_24, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.36/6.95  tff(c_4239, plain, (v3_setfam_1(k2_xboole_0('#skF_2', '#skF_3'), '#skF_1') | r2_hidden('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4227, c_30])).
% 14.36/6.95  tff(c_4248, plain, (r2_hidden('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_4219, c_4239])).
% 14.36/6.95  tff(c_28, plain, (![A_22, B_23]: (k6_subset_1(A_22, B_23)=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.36/6.95  tff(c_22, plain, (![A_13, B_14]: (m1_subset_1(k6_subset_1(A_13, B_14), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.36/6.95  tff(c_45, plain, (![A_13, B_14]: (m1_subset_1(k4_xboole_0(A_13, B_14), k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22])).
% 14.36/6.95  tff(c_14, plain, (![A_4, B_5]: (k5_xboole_0(A_4, k4_xboole_0(B_5, A_4))=k2_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.36/6.95  tff(c_91, plain, (![A_46, B_47, C_48]: (r2_hidden(A_46, B_47) | r2_hidden(A_46, C_48) | ~r2_hidden(A_46, k5_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.36/6.95  tff(c_189, plain, (![A_75, A_76, B_77]: (r2_hidden(A_75, A_76) | r2_hidden(A_75, k4_xboole_0(B_77, A_76)) | ~r2_hidden(A_75, k2_xboole_0(A_76, B_77)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_91])).
% 14.36/6.95  tff(c_24, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.36/6.95  tff(c_38292, plain, (![A_1307, A_1308, B_1309, A_1310]: (r2_hidden(A_1307, A_1308) | ~m1_subset_1(k4_xboole_0(B_1309, A_1310), k1_zfmisc_1(A_1308)) | r2_hidden(A_1307, A_1310) | ~r2_hidden(A_1307, k2_xboole_0(A_1310, B_1309)))), inference(resolution, [status(thm)], [c_189, c_24])).
% 14.36/6.95  tff(c_38300, plain, (![A_1312, A_1313, B_1314]: (r2_hidden(A_1312, A_1313) | r2_hidden(A_1312, B_1314) | ~r2_hidden(A_1312, k2_xboole_0(B_1314, A_1313)))), inference(resolution, [status(thm)], [c_45, c_38292])).
% 14.36/6.95  tff(c_38312, plain, (r2_hidden('#skF_1', '#skF_3') | r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4248, c_38300])).
% 14.36/6.95  tff(c_38323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_139, c_38312])).
% 14.36/6.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.36/6.95  
% 14.36/6.95  Inference rules
% 14.36/6.95  ----------------------
% 14.36/6.95  #Ref     : 0
% 14.36/6.95  #Sup     : 9328
% 14.36/6.95  #Fact    : 0
% 14.36/6.95  #Define  : 0
% 14.36/6.95  #Split   : 84
% 14.36/6.95  #Chain   : 0
% 14.36/6.95  #Close   : 0
% 14.36/6.95  
% 14.36/6.95  Ordering : KBO
% 14.36/6.95  
% 14.36/6.95  Simplification rules
% 14.36/6.95  ----------------------
% 14.36/6.95  #Subsume      : 154
% 14.36/6.95  #Demod        : 9480
% 14.36/6.95  #Tautology    : 1413
% 14.36/6.95  #SimpNegUnit  : 391
% 14.36/6.95  #BackRed      : 2
% 14.36/6.95  
% 14.36/6.95  #Partial instantiations: 0
% 14.36/6.95  #Strategies tried      : 1
% 14.36/6.95  
% 14.36/6.95  Timing (in seconds)
% 14.36/6.95  ----------------------
% 14.36/6.96  Preprocessing        : 0.31
% 14.36/6.96  Parsing              : 0.17
% 14.36/6.96  CNF conversion       : 0.02
% 14.36/6.96  Main loop            : 5.89
% 14.36/6.96  Inferencing          : 1.43
% 14.36/6.96  Reduction            : 2.57
% 14.36/6.96  Demodulation         : 2.03
% 14.36/6.96  BG Simplification    : 0.18
% 14.36/6.96  Subsumption          : 1.29
% 14.36/6.96  Abstraction          : 0.33
% 14.36/6.96  MUC search           : 0.00
% 14.36/6.96  Cooper               : 0.00
% 14.36/6.96  Total                : 6.23
% 14.36/6.96  Index Insertion      : 0.00
% 14.36/6.96  Index Deletion       : 0.00
% 14.36/6.96  Index Matching       : 0.00
% 14.36/6.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
