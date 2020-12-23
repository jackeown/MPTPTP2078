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
% DateTime   : Thu Dec  3 10:25:37 EST 2020

% Result     : Theorem 10.81s
% Output     : CNFRefutation 11.03s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 130 expanded)
%              Number of leaves         :   33 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 311 expanded)
%              Number of equality atoms :   18 (  49 expanded)
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

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

tff(f_76,axiom,(
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

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_66,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_56,plain,(
    ! [A_14] :
      ( r2_hidden(u1_struct_0(A_14),u1_pre_topc(A_14))
      | ~ v2_pre_topc(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_134,plain,(
    ! [A_49] :
      ( m1_subset_1(u1_pre_topc(A_49),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_49))))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_138,plain,(
    ! [A_49] :
      ( r1_tarski(u1_pre_topc(A_49),k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(resolution,[status(thm)],[c_134,c_18])).

tff(c_16,plain,(
    ! [A_11] : k3_tarski(k1_zfmisc_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k3_tarski(A_43),k3_tarski(B_44))
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_108,plain,(
    ! [A_43,A_11] :
      ( r1_tarski(k3_tarski(A_43),A_11)
      | ~ r1_tarski(A_43,k1_zfmisc_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_102])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,k3_tarski(B_8))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    ! [B_45,A_46] :
      ( B_45 = A_46
      | ~ r1_tarski(B_45,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_180,plain,(
    ! [B_62,A_63] :
      ( k3_tarski(B_62) = A_63
      | ~ r1_tarski(k3_tarski(B_62),A_63)
      | ~ r2_hidden(A_63,B_62) ) ),
    inference(resolution,[status(thm)],[c_12,c_109])).

tff(c_220,plain,(
    ! [A_67,A_68] :
      ( k3_tarski(A_67) = A_68
      | ~ r2_hidden(A_68,A_67)
      | ~ r1_tarski(A_67,k1_zfmisc_1(A_68)) ) ),
    inference(resolution,[status(thm)],[c_108,c_180])).

tff(c_525,plain,(
    ! [A_107] :
      ( k3_tarski(u1_pre_topc(A_107)) = u1_struct_0(A_107)
      | ~ r2_hidden(u1_struct_0(A_107),u1_pre_topc(A_107))
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_138,c_220])).

tff(c_529,plain,(
    ! [A_14] :
      ( k3_tarski(u1_pre_topc(A_14)) = u1_struct_0(A_14)
      | ~ v2_pre_topc(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(resolution,[status(thm)],[c_56,c_525])).

tff(c_530,plain,(
    ! [A_108] :
      ( k3_tarski(u1_pre_topc(A_108)) = u1_struct_0(A_108)
      | ~ v2_pre_topc(A_108)
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_56,c_525])).

tff(c_60,plain,(
    ! [A_29] :
      ( k4_yellow_0(k2_yellow_1(A_29)) = k3_tarski(A_29)
      | ~ r2_hidden(k3_tarski(A_29),A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6400,plain,(
    ! [A_598] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_598))) = k3_tarski(u1_pre_topc(A_598))
      | ~ r2_hidden(u1_struct_0(A_598),u1_pre_topc(A_598))
      | v1_xboole_0(u1_pre_topc(A_598))
      | ~ v2_pre_topc(A_598)
      | ~ l1_pre_topc(A_598) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_60])).

tff(c_6405,plain,(
    ! [A_599] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_599))) = k3_tarski(u1_pre_topc(A_599))
      | v1_xboole_0(u1_pre_topc(A_599))
      | ~ v2_pre_topc(A_599)
      | ~ l1_pre_topc(A_599) ) ),
    inference(resolution,[status(thm)],[c_56,c_6400])).

tff(c_62,plain,(
    k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_5'))) != u1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6411,plain,
    ( k3_tarski(u1_pre_topc('#skF_5')) != u1_struct_0('#skF_5')
    | v1_xboole_0(u1_pre_topc('#skF_5'))
    | ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6405,c_62])).

tff(c_6417,plain,
    ( k3_tarski(u1_pre_topc('#skF_5')) != u1_struct_0('#skF_5')
    | v1_xboole_0(u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_6411])).

tff(c_6419,plain,(
    k3_tarski(u1_pre_topc('#skF_5')) != u1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6417])).

tff(c_6422,plain,
    ( ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_6419])).

tff(c_6426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_6422])).

tff(c_6427,plain,(
    v1_xboole_0(u1_pre_topc('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6417])).

tff(c_154,plain,(
    ! [A_54] :
      ( r2_hidden(u1_struct_0(A_54),u1_pre_topc(A_54))
      | ~ v2_pre_topc(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_158,plain,(
    ! [A_54] :
      ( ~ v1_xboole_0(u1_pre_topc(A_54))
      | ~ v2_pre_topc(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_154,c_2])).

tff(c_6431,plain,
    ( ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_6427,c_158])).

tff(c_6435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_6431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:25:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.81/3.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.97/3.87  
% 10.97/3.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.97/3.87  %$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_2 > #skF_4 > #skF_1 > #skF_5 > #skF_3
% 10.97/3.87  
% 10.97/3.87  %Foreground sorts:
% 10.97/3.87  
% 10.97/3.87  
% 10.97/3.87  %Background operators:
% 10.97/3.87  
% 10.97/3.87  
% 10.97/3.87  %Foreground operators:
% 10.97/3.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.97/3.87  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 10.97/3.87  tff('#skF_2', type, '#skF_2': $i > $i).
% 10.97/3.87  tff('#skF_4', type, '#skF_4': $i > $i).
% 10.97/3.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.97/3.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.97/3.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.97/3.87  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 10.97/3.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.97/3.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.97/3.87  tff('#skF_5', type, '#skF_5': $i).
% 10.97/3.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.97/3.87  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 10.97/3.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.97/3.87  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.97/3.87  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 10.97/3.87  tff('#skF_3', type, '#skF_3': $i > $i).
% 10.97/3.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.97/3.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.97/3.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.97/3.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.97/3.87  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.97/3.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.97/3.87  
% 11.03/3.88  tff(f_97, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 11.03/3.88  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 11.03/3.88  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 11.03/3.88  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.03/3.88  tff(f_47, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 11.03/3.88  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 11.03/3.88  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 11.03/3.88  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.03/3.88  tff(f_87, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 11.03/3.88  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.03/3.88  tff(c_64, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.03/3.88  tff(c_66, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.03/3.88  tff(c_56, plain, (![A_14]: (r2_hidden(u1_struct_0(A_14), u1_pre_topc(A_14)) | ~v2_pre_topc(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.03/3.88  tff(c_134, plain, (![A_49]: (m1_subset_1(u1_pre_topc(A_49), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_49)))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.03/3.88  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.03/3.88  tff(c_138, plain, (![A_49]: (r1_tarski(u1_pre_topc(A_49), k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(resolution, [status(thm)], [c_134, c_18])).
% 11.03/3.88  tff(c_16, plain, (![A_11]: (k3_tarski(k1_zfmisc_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.03/3.88  tff(c_102, plain, (![A_43, B_44]: (r1_tarski(k3_tarski(A_43), k3_tarski(B_44)) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.03/3.88  tff(c_108, plain, (![A_43, A_11]: (r1_tarski(k3_tarski(A_43), A_11) | ~r1_tarski(A_43, k1_zfmisc_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_102])).
% 11.03/3.88  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, k3_tarski(B_8)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.03/3.88  tff(c_109, plain, (![B_45, A_46]: (B_45=A_46 | ~r1_tarski(B_45, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.03/3.88  tff(c_180, plain, (![B_62, A_63]: (k3_tarski(B_62)=A_63 | ~r1_tarski(k3_tarski(B_62), A_63) | ~r2_hidden(A_63, B_62))), inference(resolution, [status(thm)], [c_12, c_109])).
% 11.03/3.88  tff(c_220, plain, (![A_67, A_68]: (k3_tarski(A_67)=A_68 | ~r2_hidden(A_68, A_67) | ~r1_tarski(A_67, k1_zfmisc_1(A_68)))), inference(resolution, [status(thm)], [c_108, c_180])).
% 11.03/3.88  tff(c_525, plain, (![A_107]: (k3_tarski(u1_pre_topc(A_107))=u1_struct_0(A_107) | ~r2_hidden(u1_struct_0(A_107), u1_pre_topc(A_107)) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_138, c_220])).
% 11.03/3.88  tff(c_529, plain, (![A_14]: (k3_tarski(u1_pre_topc(A_14))=u1_struct_0(A_14) | ~v2_pre_topc(A_14) | ~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_56, c_525])).
% 11.03/3.88  tff(c_530, plain, (![A_108]: (k3_tarski(u1_pre_topc(A_108))=u1_struct_0(A_108) | ~v2_pre_topc(A_108) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_56, c_525])).
% 11.03/3.88  tff(c_60, plain, (![A_29]: (k4_yellow_0(k2_yellow_1(A_29))=k3_tarski(A_29) | ~r2_hidden(k3_tarski(A_29), A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.03/3.88  tff(c_6400, plain, (![A_598]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_598)))=k3_tarski(u1_pre_topc(A_598)) | ~r2_hidden(u1_struct_0(A_598), u1_pre_topc(A_598)) | v1_xboole_0(u1_pre_topc(A_598)) | ~v2_pre_topc(A_598) | ~l1_pre_topc(A_598))), inference(superposition, [status(thm), theory('equality')], [c_530, c_60])).
% 11.03/3.88  tff(c_6405, plain, (![A_599]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_599)))=k3_tarski(u1_pre_topc(A_599)) | v1_xboole_0(u1_pre_topc(A_599)) | ~v2_pre_topc(A_599) | ~l1_pre_topc(A_599))), inference(resolution, [status(thm)], [c_56, c_6400])).
% 11.03/3.88  tff(c_62, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_5')))!=u1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.03/3.88  tff(c_6411, plain, (k3_tarski(u1_pre_topc('#skF_5'))!=u1_struct_0('#skF_5') | v1_xboole_0(u1_pre_topc('#skF_5')) | ~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6405, c_62])).
% 11.03/3.88  tff(c_6417, plain, (k3_tarski(u1_pre_topc('#skF_5'))!=u1_struct_0('#skF_5') | v1_xboole_0(u1_pre_topc('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_6411])).
% 11.03/3.88  tff(c_6419, plain, (k3_tarski(u1_pre_topc('#skF_5'))!=u1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_6417])).
% 11.03/3.88  tff(c_6422, plain, (~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_529, c_6419])).
% 11.03/3.88  tff(c_6426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_6422])).
% 11.03/3.88  tff(c_6427, plain, (v1_xboole_0(u1_pre_topc('#skF_5'))), inference(splitRight, [status(thm)], [c_6417])).
% 11.03/3.88  tff(c_154, plain, (![A_54]: (r2_hidden(u1_struct_0(A_54), u1_pre_topc(A_54)) | ~v2_pre_topc(A_54) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.03/3.88  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.03/3.88  tff(c_158, plain, (![A_54]: (~v1_xboole_0(u1_pre_topc(A_54)) | ~v2_pre_topc(A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_154, c_2])).
% 11.03/3.88  tff(c_6431, plain, (~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_6427, c_158])).
% 11.03/3.88  tff(c_6435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_6431])).
% 11.03/3.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.03/3.88  
% 11.03/3.88  Inference rules
% 11.03/3.88  ----------------------
% 11.03/3.88  #Ref     : 0
% 11.03/3.88  #Sup     : 1668
% 11.03/3.88  #Fact    : 0
% 11.03/3.88  #Define  : 0
% 11.03/3.88  #Split   : 1
% 11.03/3.88  #Chain   : 0
% 11.03/3.88  #Close   : 0
% 11.03/3.88  
% 11.03/3.88  Ordering : KBO
% 11.03/3.88  
% 11.03/3.88  Simplification rules
% 11.03/3.88  ----------------------
% 11.03/3.88  #Subsume      : 136
% 11.03/3.88  #Demod        : 293
% 11.03/3.88  #Tautology    : 149
% 11.03/3.88  #SimpNegUnit  : 0
% 11.03/3.88  #BackRed      : 0
% 11.03/3.88  
% 11.03/3.88  #Partial instantiations: 0
% 11.03/3.88  #Strategies tried      : 1
% 11.03/3.88  
% 11.03/3.88  Timing (in seconds)
% 11.03/3.88  ----------------------
% 11.03/3.88  Preprocessing        : 0.31
% 11.03/3.88  Parsing              : 0.16
% 11.03/3.88  CNF conversion       : 0.03
% 11.03/3.88  Main loop            : 2.81
% 11.03/3.88  Inferencing          : 0.53
% 11.03/3.88  Reduction            : 0.42
% 11.03/3.88  Demodulation         : 0.26
% 11.03/3.88  BG Simplification    : 0.08
% 11.03/3.88  Subsumption          : 1.65
% 11.03/3.89  Abstraction          : 0.08
% 11.03/3.89  MUC search           : 0.00
% 11.03/3.89  Cooper               : 0.00
% 11.03/3.89  Total                : 3.16
% 11.03/3.89  Index Insertion      : 0.00
% 11.03/3.89  Index Deletion       : 0.00
% 11.03/3.89  Index Matching       : 0.00
% 11.03/3.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
