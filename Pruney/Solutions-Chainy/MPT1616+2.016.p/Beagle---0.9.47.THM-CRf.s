%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:37 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 124 expanded)
%              Number of leaves         :   33 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 309 expanded)
%              Number of equality atoms :   16 (  40 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_2 > #skF_4 > #skF_1 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

tff(f_80,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_64,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_66,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_56,plain,(
    ! [A_16] :
      ( r2_hidden(u1_struct_0(A_16),u1_pre_topc(A_16))
      | ~ v2_pre_topc(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_58,plain,(
    ! [A_30] :
      ( m1_subset_1(u1_pre_topc(A_30),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_30))))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_109,plain,(
    ! [A_48,B_49] :
      ( k5_setfam_1(A_48,B_49) = k3_tarski(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_117,plain,(
    ! [A_30] :
      ( k5_setfam_1(u1_struct_0(A_30),u1_pre_topc(A_30)) = k3_tarski(u1_pre_topc(A_30))
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_58,c_109])).

tff(c_305,plain,(
    ! [A_98,B_99] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_98),B_99),u1_pre_topc(A_98))
      | ~ r1_tarski(B_99,u1_pre_topc(A_98))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_98))))
      | ~ v2_pre_topc(A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_318,plain,(
    ! [A_30] :
      ( r2_hidden(k3_tarski(u1_pre_topc(A_30)),u1_pre_topc(A_30))
      | ~ r1_tarski(u1_pre_topc(A_30),u1_pre_topc(A_30))
      | ~ m1_subset_1(u1_pre_topc(A_30),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_30))))
      | ~ v2_pre_topc(A_30)
      | ~ l1_pre_topc(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_305])).

tff(c_400,plain,(
    ! [A_111] :
      ( r2_hidden(k3_tarski(u1_pre_topc(A_111)),u1_pre_topc(A_111))
      | ~ m1_subset_1(u1_pre_topc(A_111),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_111))))
      | ~ v2_pre_topc(A_111)
      | ~ l1_pre_topc(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_318])).

tff(c_421,plain,(
    ! [A_113] :
      ( r2_hidden(k3_tarski(u1_pre_topc(A_113)),u1_pre_topc(A_113))
      | ~ v2_pre_topc(A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_58,c_400])).

tff(c_138,plain,(
    ! [A_53,C_54,B_55] :
      ( m1_subset_1(A_53,C_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(C_54))
      | ~ r2_hidden(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_203,plain,(
    ! [A_68,A_69] :
      ( m1_subset_1(A_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ r2_hidden(A_68,u1_pre_topc(A_69))
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_58,c_138])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_210,plain,(
    ! [A_68,A_69] :
      ( r1_tarski(A_68,u1_struct_0(A_69))
      | ~ r2_hidden(A_68,u1_pre_topc(A_69))
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_203,c_16])).

tff(c_444,plain,(
    ! [A_114] :
      ( r1_tarski(k3_tarski(u1_pre_topc(A_114)),u1_struct_0(A_114))
      | ~ v2_pre_topc(A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_421,c_210])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,k3_tarski(B_8))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_84,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ r1_tarski(B_42,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89,plain,(
    ! [B_8,A_7] :
      ( k3_tarski(B_8) = A_7
      | ~ r1_tarski(k3_tarski(B_8),A_7)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_84])).

tff(c_510,plain,(
    ! [A_121] :
      ( k3_tarski(u1_pre_topc(A_121)) = u1_struct_0(A_121)
      | ~ r2_hidden(u1_struct_0(A_121),u1_pre_topc(A_121))
      | ~ v2_pre_topc(A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(resolution,[status(thm)],[c_444,c_89])).

tff(c_527,plain,(
    ! [A_123] :
      ( k3_tarski(u1_pre_topc(A_123)) = u1_struct_0(A_123)
      | ~ v2_pre_topc(A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_56,c_510])).

tff(c_60,plain,(
    ! [A_31] :
      ( k4_yellow_0(k2_yellow_1(A_31)) = k3_tarski(A_31)
      | ~ r2_hidden(k3_tarski(A_31),A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_473,plain,(
    ! [A_118] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_118))) = k3_tarski(u1_pre_topc(A_118))
      | v1_xboole_0(u1_pre_topc(A_118))
      | ~ v2_pre_topc(A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_421,c_60])).

tff(c_62,plain,(
    k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_5'))) != u1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_479,plain,
    ( k3_tarski(u1_pre_topc('#skF_5')) != u1_struct_0('#skF_5')
    | v1_xboole_0(u1_pre_topc('#skF_5'))
    | ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_62])).

tff(c_485,plain,
    ( k3_tarski(u1_pre_topc('#skF_5')) != u1_struct_0('#skF_5')
    | v1_xboole_0(u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_479])).

tff(c_487,plain,(
    k3_tarski(u1_pre_topc('#skF_5')) != u1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_485])).

tff(c_536,plain,
    ( ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_487])).

tff(c_567,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_536])).

tff(c_568,plain,(
    v1_xboole_0(u1_pre_topc('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_103,plain,(
    ! [A_46] :
      ( r2_hidden(u1_struct_0(A_46),u1_pre_topc(A_46))
      | ~ v2_pre_topc(A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(u1_pre_topc(A_46))
      | ~ v2_pre_topc(A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_572,plain,
    ( ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_568,c_107])).

tff(c_576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_572])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:29:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.38  
% 2.84/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.38  %$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_2 > #skF_4 > #skF_1 > #skF_5 > #skF_3
% 2.84/1.38  
% 2.84/1.38  %Foreground sorts:
% 2.84/1.38  
% 2.84/1.38  
% 2.84/1.38  %Background operators:
% 2.84/1.38  
% 2.84/1.38  
% 2.84/1.38  %Foreground operators:
% 2.84/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.84/1.38  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.84/1.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.84/1.38  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.84/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.84/1.38  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.84/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.84/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.84/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.38  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.84/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.84/1.38  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 2.84/1.38  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.84/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.84/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.84/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.84/1.38  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.84/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.38  
% 2.84/1.39  tff(f_101, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 2.84/1.39  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 2.84/1.39  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.84/1.39  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.84/1.39  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.84/1.39  tff(f_55, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.84/1.39  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.84/1.39  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.84/1.39  tff(f_91, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 2.84/1.39  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.84/1.39  tff(c_64, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.84/1.39  tff(c_66, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.84/1.39  tff(c_56, plain, (![A_16]: (r2_hidden(u1_struct_0(A_16), u1_pre_topc(A_16)) | ~v2_pre_topc(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.84/1.39  tff(c_58, plain, (![A_30]: (m1_subset_1(u1_pre_topc(A_30), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_30)))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.84/1.39  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.84/1.39  tff(c_109, plain, (![A_48, B_49]: (k5_setfam_1(A_48, B_49)=k3_tarski(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.84/1.39  tff(c_117, plain, (![A_30]: (k5_setfam_1(u1_struct_0(A_30), u1_pre_topc(A_30))=k3_tarski(u1_pre_topc(A_30)) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_58, c_109])).
% 2.84/1.39  tff(c_305, plain, (![A_98, B_99]: (r2_hidden(k5_setfam_1(u1_struct_0(A_98), B_99), u1_pre_topc(A_98)) | ~r1_tarski(B_99, u1_pre_topc(A_98)) | ~m1_subset_1(B_99, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_98)))) | ~v2_pre_topc(A_98) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.84/1.39  tff(c_318, plain, (![A_30]: (r2_hidden(k3_tarski(u1_pre_topc(A_30)), u1_pre_topc(A_30)) | ~r1_tarski(u1_pre_topc(A_30), u1_pre_topc(A_30)) | ~m1_subset_1(u1_pre_topc(A_30), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_30)))) | ~v2_pre_topc(A_30) | ~l1_pre_topc(A_30) | ~l1_pre_topc(A_30))), inference(superposition, [status(thm), theory('equality')], [c_117, c_305])).
% 2.84/1.39  tff(c_400, plain, (![A_111]: (r2_hidden(k3_tarski(u1_pre_topc(A_111)), u1_pre_topc(A_111)) | ~m1_subset_1(u1_pre_topc(A_111), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_111)))) | ~v2_pre_topc(A_111) | ~l1_pre_topc(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_318])).
% 2.84/1.39  tff(c_421, plain, (![A_113]: (r2_hidden(k3_tarski(u1_pre_topc(A_113)), u1_pre_topc(A_113)) | ~v2_pre_topc(A_113) | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_58, c_400])).
% 2.84/1.39  tff(c_138, plain, (![A_53, C_54, B_55]: (m1_subset_1(A_53, C_54) | ~m1_subset_1(B_55, k1_zfmisc_1(C_54)) | ~r2_hidden(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.84/1.39  tff(c_203, plain, (![A_68, A_69]: (m1_subset_1(A_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~r2_hidden(A_68, u1_pre_topc(A_69)) | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_58, c_138])).
% 2.84/1.39  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.84/1.39  tff(c_210, plain, (![A_68, A_69]: (r1_tarski(A_68, u1_struct_0(A_69)) | ~r2_hidden(A_68, u1_pre_topc(A_69)) | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_203, c_16])).
% 2.84/1.39  tff(c_444, plain, (![A_114]: (r1_tarski(k3_tarski(u1_pre_topc(A_114)), u1_struct_0(A_114)) | ~v2_pre_topc(A_114) | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_421, c_210])).
% 2.84/1.39  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, k3_tarski(B_8)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.84/1.39  tff(c_84, plain, (![B_42, A_43]: (B_42=A_43 | ~r1_tarski(B_42, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.84/1.39  tff(c_89, plain, (![B_8, A_7]: (k3_tarski(B_8)=A_7 | ~r1_tarski(k3_tarski(B_8), A_7) | ~r2_hidden(A_7, B_8))), inference(resolution, [status(thm)], [c_12, c_84])).
% 2.84/1.39  tff(c_510, plain, (![A_121]: (k3_tarski(u1_pre_topc(A_121))=u1_struct_0(A_121) | ~r2_hidden(u1_struct_0(A_121), u1_pre_topc(A_121)) | ~v2_pre_topc(A_121) | ~l1_pre_topc(A_121))), inference(resolution, [status(thm)], [c_444, c_89])).
% 2.84/1.39  tff(c_527, plain, (![A_123]: (k3_tarski(u1_pre_topc(A_123))=u1_struct_0(A_123) | ~v2_pre_topc(A_123) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_56, c_510])).
% 2.84/1.39  tff(c_60, plain, (![A_31]: (k4_yellow_0(k2_yellow_1(A_31))=k3_tarski(A_31) | ~r2_hidden(k3_tarski(A_31), A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.84/1.39  tff(c_473, plain, (![A_118]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_118)))=k3_tarski(u1_pre_topc(A_118)) | v1_xboole_0(u1_pre_topc(A_118)) | ~v2_pre_topc(A_118) | ~l1_pre_topc(A_118))), inference(resolution, [status(thm)], [c_421, c_60])).
% 2.84/1.39  tff(c_62, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_5')))!=u1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.84/1.39  tff(c_479, plain, (k3_tarski(u1_pre_topc('#skF_5'))!=u1_struct_0('#skF_5') | v1_xboole_0(u1_pre_topc('#skF_5')) | ~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_473, c_62])).
% 2.84/1.39  tff(c_485, plain, (k3_tarski(u1_pre_topc('#skF_5'))!=u1_struct_0('#skF_5') | v1_xboole_0(u1_pre_topc('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_479])).
% 2.84/1.39  tff(c_487, plain, (k3_tarski(u1_pre_topc('#skF_5'))!=u1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_485])).
% 2.84/1.39  tff(c_536, plain, (~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_527, c_487])).
% 2.84/1.39  tff(c_567, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_536])).
% 2.84/1.39  tff(c_568, plain, (v1_xboole_0(u1_pre_topc('#skF_5'))), inference(splitRight, [status(thm)], [c_485])).
% 2.84/1.39  tff(c_103, plain, (![A_46]: (r2_hidden(u1_struct_0(A_46), u1_pre_topc(A_46)) | ~v2_pre_topc(A_46) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.84/1.39  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.39  tff(c_107, plain, (![A_46]: (~v1_xboole_0(u1_pre_topc(A_46)) | ~v2_pre_topc(A_46) | ~l1_pre_topc(A_46))), inference(resolution, [status(thm)], [c_103, c_2])).
% 2.84/1.39  tff(c_572, plain, (~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_568, c_107])).
% 2.84/1.39  tff(c_576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_572])).
% 2.84/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.39  
% 2.84/1.39  Inference rules
% 2.84/1.39  ----------------------
% 2.84/1.39  #Ref     : 0
% 2.84/1.39  #Sup     : 111
% 2.84/1.39  #Fact    : 0
% 2.84/1.39  #Define  : 0
% 2.84/1.39  #Split   : 1
% 2.84/1.39  #Chain   : 0
% 2.84/1.40  #Close   : 0
% 2.84/1.40  
% 2.84/1.40  Ordering : KBO
% 2.84/1.40  
% 2.84/1.40  Simplification rules
% 2.84/1.40  ----------------------
% 2.84/1.40  #Subsume      : 6
% 2.84/1.40  #Demod        : 11
% 2.84/1.40  #Tautology    : 21
% 2.84/1.40  #SimpNegUnit  : 0
% 2.84/1.40  #BackRed      : 0
% 2.84/1.40  
% 2.84/1.40  #Partial instantiations: 0
% 2.84/1.40  #Strategies tried      : 1
% 2.84/1.40  
% 2.84/1.40  Timing (in seconds)
% 2.84/1.40  ----------------------
% 2.84/1.40  Preprocessing        : 0.31
% 2.84/1.40  Parsing              : 0.16
% 2.84/1.40  CNF conversion       : 0.02
% 2.84/1.40  Main loop            : 0.32
% 2.84/1.40  Inferencing          : 0.12
% 2.84/1.40  Reduction            : 0.08
% 2.84/1.40  Demodulation         : 0.05
% 2.84/1.40  BG Simplification    : 0.02
% 2.84/1.40  Subsumption          : 0.07
% 2.84/1.40  Abstraction          : 0.02
% 2.84/1.40  MUC search           : 0.00
% 2.84/1.40  Cooper               : 0.00
% 2.84/1.40  Total                : 0.66
% 2.84/1.40  Index Insertion      : 0.00
% 2.84/1.40  Index Deletion       : 0.00
% 2.84/1.40  Index Matching       : 0.00
% 2.84/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
