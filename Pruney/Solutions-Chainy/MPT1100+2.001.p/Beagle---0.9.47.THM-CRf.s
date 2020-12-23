%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:28 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   56 (  63 expanded)
%              Number of leaves         :   33 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :   71 (  88 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_4 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => r2_hidden(k1_xboole_0,u1_pre_topc(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).

tff(f_71,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_xboole_0(C,B) )
     => r1_xboole_0(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

tff(c_66,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_68,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_22,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_143,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_2'(A_55,B_56),A_55)
      | r1_xboole_0(k3_tarski(A_55),B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_89,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = k1_xboole_0
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_101,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_89])).

tff(c_113,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r1_xboole_0(A_46,B_47)
      | ~ r2_hidden(C_48,k3_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_116,plain,(
    ! [C_48] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(C_48,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_113])).

tff(c_118,plain,(
    ! [C_48] : ~ r2_hidden(C_48,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_116])).

tff(c_160,plain,(
    ! [B_59] : r1_xboole_0(k3_tarski(k1_xboole_0),B_59) ),
    inference(resolution,[status(thm)],[c_143,c_118])).

tff(c_14,plain,(
    ! [A_9] :
      ( ~ r1_xboole_0(A_9,A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_169,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_160,c_14])).

tff(c_154,plain,(
    ! [A_57,B_58] :
      ( k5_setfam_1(A_57,B_58) = k3_tarski(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_159,plain,(
    ! [A_57] : k5_setfam_1(A_57,k1_xboole_0) = k3_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_154])).

tff(c_206,plain,(
    ! [A_57] : k5_setfam_1(A_57,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_159])).

tff(c_351,plain,(
    ! [A_83,B_84] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_83),B_84),u1_pre_topc(A_83))
      | ~ r1_tarski(B_84,u1_pre_topc(A_83))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_83))))
      | ~ v2_pre_topc(A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_355,plain,(
    ! [A_83] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_83))
      | ~ r1_tarski(k1_xboole_0,u1_pre_topc(A_83))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_83))))
      | ~ v2_pre_topc(A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_351])).

tff(c_358,plain,(
    ! [A_85] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_85))
      | ~ v2_pre_topc(A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_10,c_355])).

tff(c_64,plain,(
    ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_361,plain,
    ( ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_358,c_64])).

tff(c_365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_361])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.33  
% 2.20/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_4 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 2.20/1.33  
% 2.20/1.33  %Foreground sorts:
% 2.20/1.33  
% 2.20/1.33  
% 2.20/1.33  %Background operators:
% 2.20/1.33  
% 2.20/1.33  
% 2.20/1.33  %Foreground operators:
% 2.20/1.33  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.20/1.33  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.20/1.33  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.20/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.20/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.20/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.20/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.20/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.33  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.20/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.20/1.33  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.20/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.20/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.20/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.20/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.20/1.33  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.20/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.33  
% 2.54/1.35  tff(f_113, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => r2_hidden(k1_xboole_0, u1_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_pre_topc)).
% 2.54/1.35  tff(f_71, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.54/1.35  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.54/1.35  tff(f_69, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_xboole_0(C, B))) => r1_xboole_0(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 2.54/1.35  tff(f_57, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.54/1.35  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.54/1.35  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.54/1.35  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.54/1.35  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 2.54/1.35  tff(c_66, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.54/1.35  tff(c_68, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.54/1.35  tff(c_22, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.54/1.35  tff(c_10, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.54/1.35  tff(c_143, plain, (![A_55, B_56]: (r2_hidden('#skF_2'(A_55, B_56), A_55) | r1_xboole_0(k3_tarski(A_55), B_56))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.54/1.35  tff(c_12, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.54/1.35  tff(c_89, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=k1_xboole_0 | ~r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.54/1.35  tff(c_101, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_89])).
% 2.54/1.35  tff(c_113, plain, (![A_46, B_47, C_48]: (~r1_xboole_0(A_46, B_47) | ~r2_hidden(C_48, k3_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.54/1.35  tff(c_116, plain, (![C_48]: (~r1_xboole_0(k1_xboole_0, k1_xboole_0) | ~r2_hidden(C_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_101, c_113])).
% 2.54/1.35  tff(c_118, plain, (![C_48]: (~r2_hidden(C_48, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_116])).
% 2.54/1.35  tff(c_160, plain, (![B_59]: (r1_xboole_0(k3_tarski(k1_xboole_0), B_59))), inference(resolution, [status(thm)], [c_143, c_118])).
% 2.54/1.35  tff(c_14, plain, (![A_9]: (~r1_xboole_0(A_9, A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.54/1.35  tff(c_169, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_160, c_14])).
% 2.54/1.35  tff(c_154, plain, (![A_57, B_58]: (k5_setfam_1(A_57, B_58)=k3_tarski(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.54/1.35  tff(c_159, plain, (![A_57]: (k5_setfam_1(A_57, k1_xboole_0)=k3_tarski(k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_154])).
% 2.54/1.35  tff(c_206, plain, (![A_57]: (k5_setfam_1(A_57, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_169, c_159])).
% 2.54/1.35  tff(c_351, plain, (![A_83, B_84]: (r2_hidden(k5_setfam_1(u1_struct_0(A_83), B_84), u1_pre_topc(A_83)) | ~r1_tarski(B_84, u1_pre_topc(A_83)) | ~m1_subset_1(B_84, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_83)))) | ~v2_pre_topc(A_83) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.54/1.35  tff(c_355, plain, (![A_83]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_83)) | ~r1_tarski(k1_xboole_0, u1_pre_topc(A_83)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_83)))) | ~v2_pre_topc(A_83) | ~l1_pre_topc(A_83))), inference(superposition, [status(thm), theory('equality')], [c_206, c_351])).
% 2.54/1.35  tff(c_358, plain, (![A_85]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_85)) | ~v2_pre_topc(A_85) | ~l1_pre_topc(A_85))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_10, c_355])).
% 2.54/1.35  tff(c_64, plain, (~r2_hidden(k1_xboole_0, u1_pre_topc('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.54/1.35  tff(c_361, plain, (~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_358, c_64])).
% 2.54/1.35  tff(c_365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_361])).
% 2.54/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.35  
% 2.54/1.35  Inference rules
% 2.54/1.35  ----------------------
% 2.54/1.35  #Ref     : 0
% 2.54/1.35  #Sup     : 63
% 2.54/1.35  #Fact    : 0
% 2.54/1.35  #Define  : 0
% 2.54/1.35  #Split   : 0
% 2.54/1.35  #Chain   : 0
% 2.54/1.35  #Close   : 0
% 2.54/1.35  
% 2.54/1.35  Ordering : KBO
% 2.54/1.35  
% 2.54/1.35  Simplification rules
% 2.54/1.35  ----------------------
% 2.54/1.35  #Subsume      : 8
% 2.54/1.35  #Demod        : 35
% 2.54/1.35  #Tautology    : 38
% 2.54/1.35  #SimpNegUnit  : 3
% 2.54/1.35  #BackRed      : 1
% 2.54/1.35  
% 2.54/1.35  #Partial instantiations: 0
% 2.54/1.35  #Strategies tried      : 1
% 2.54/1.35  
% 2.54/1.35  Timing (in seconds)
% 2.54/1.35  ----------------------
% 2.54/1.35  Preprocessing        : 0.34
% 2.54/1.35  Parsing              : 0.17
% 2.54/1.35  CNF conversion       : 0.02
% 2.54/1.35  Main loop            : 0.22
% 2.54/1.35  Inferencing          : 0.08
% 2.54/1.35  Reduction            : 0.07
% 2.54/1.35  Demodulation         : 0.05
% 2.54/1.35  BG Simplification    : 0.02
% 2.54/1.35  Subsumption          : 0.04
% 2.54/1.35  Abstraction          : 0.01
% 2.54/1.35  MUC search           : 0.00
% 2.54/1.35  Cooper               : 0.00
% 2.54/1.35  Total                : 0.60
% 2.54/1.35  Index Insertion      : 0.00
% 2.54/1.35  Index Deletion       : 0.00
% 2.54/1.35  Index Matching       : 0.00
% 2.54/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
