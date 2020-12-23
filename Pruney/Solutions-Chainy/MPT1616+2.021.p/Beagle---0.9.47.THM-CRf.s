%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:38 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 139 expanded)
%              Number of leaves         :   33 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  111 ( 344 expanded)
%              Number of equality atoms :   17 (  49 expanded)
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

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
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

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_43,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_64,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_66,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_136,plain,(
    ! [A_52] :
      ( m1_subset_1(u1_pre_topc(A_52),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_52))))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_140,plain,(
    ! [A_52] :
      ( r1_tarski(u1_pre_topc(A_52),k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_136,c_16])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_56,plain,(
    ! [A_15] :
      ( r2_hidden(u1_struct_0(A_15),u1_pre_topc(A_15))
      | ~ v2_pre_topc(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_145,plain,(
    ! [C_54,B_55,A_56] :
      ( r1_tarski(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(k3_tarski(A_56),B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_428,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(u1_struct_0(A_92),B_93)
      | ~ r1_tarski(k3_tarski(u1_pre_topc(A_92)),B_93)
      | ~ v2_pre_topc(A_92)
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_56,c_145])).

tff(c_444,plain,(
    ! [A_94] :
      ( r1_tarski(u1_struct_0(A_94),k3_tarski(u1_pre_topc(A_94)))
      | ~ v2_pre_topc(A_94)
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_10,c_428])).

tff(c_14,plain,(
    ! [A_9] : k3_tarski(k1_zfmisc_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_99,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k3_tarski(A_42),k3_tarski(B_43))
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_116,plain,(
    ! [A_46,A_47] :
      ( r1_tarski(k3_tarski(A_46),A_47)
      | ~ r1_tarski(A_46,k1_zfmisc_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_99])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_122,plain,(
    ! [A_46,A_47] :
      ( k3_tarski(A_46) = A_47
      | ~ r1_tarski(A_47,k3_tarski(A_46))
      | ~ r1_tarski(A_46,k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_116,c_6])).

tff(c_842,plain,(
    ! [A_141] :
      ( k3_tarski(u1_pre_topc(A_141)) = u1_struct_0(A_141)
      | ~ r1_tarski(u1_pre_topc(A_141),k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ v2_pre_topc(A_141)
      | ~ l1_pre_topc(A_141) ) ),
    inference(resolution,[status(thm)],[c_444,c_122])).

tff(c_846,plain,(
    ! [A_52] :
      ( k3_tarski(u1_pre_topc(A_52)) = u1_struct_0(A_52)
      | ~ v2_pre_topc(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_140,c_842])).

tff(c_847,plain,(
    ! [A_142] :
      ( k3_tarski(u1_pre_topc(A_142)) = u1_struct_0(A_142)
      | ~ v2_pre_topc(A_142)
      | ~ l1_pre_topc(A_142) ) ),
    inference(resolution,[status(thm)],[c_140,c_842])).

tff(c_60,plain,(
    ! [A_30] :
      ( k4_yellow_0(k2_yellow_1(A_30)) = k3_tarski(A_30)
      | ~ r2_hidden(k3_tarski(A_30),A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3694,plain,(
    ! [A_328] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_328))) = k3_tarski(u1_pre_topc(A_328))
      | ~ r2_hidden(u1_struct_0(A_328),u1_pre_topc(A_328))
      | v1_xboole_0(u1_pre_topc(A_328))
      | ~ v2_pre_topc(A_328)
      | ~ l1_pre_topc(A_328) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_847,c_60])).

tff(c_3699,plain,(
    ! [A_329] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_329))) = k3_tarski(u1_pre_topc(A_329))
      | v1_xboole_0(u1_pre_topc(A_329))
      | ~ v2_pre_topc(A_329)
      | ~ l1_pre_topc(A_329) ) ),
    inference(resolution,[status(thm)],[c_56,c_3694])).

tff(c_62,plain,(
    k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_5'))) != u1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3705,plain,
    ( k3_tarski(u1_pre_topc('#skF_5')) != u1_struct_0('#skF_5')
    | v1_xboole_0(u1_pre_topc('#skF_5'))
    | ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3699,c_62])).

tff(c_3711,plain,
    ( k3_tarski(u1_pre_topc('#skF_5')) != u1_struct_0('#skF_5')
    | v1_xboole_0(u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_3705])).

tff(c_3713,plain,(
    k3_tarski(u1_pre_topc('#skF_5')) != u1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3711])).

tff(c_3716,plain,
    ( ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_846,c_3713])).

tff(c_3720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_3716])).

tff(c_3721,plain,(
    v1_xboole_0(u1_pre_topc('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3711])).

tff(c_130,plain,(
    ! [A_50] :
      ( r2_hidden(u1_struct_0(A_50),u1_pre_topc(A_50))
      | ~ v2_pre_topc(A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [A_50] :
      ( ~ v1_xboole_0(u1_pre_topc(A_50))
      | ~ v2_pre_topc(A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(resolution,[status(thm)],[c_130,c_2])).

tff(c_3725,plain,
    ( ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_3721,c_134])).

tff(c_3729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_3725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:28:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.58/2.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.58  
% 7.58/2.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.58  %$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_2 > #skF_4 > #skF_1 > #skF_5 > #skF_3
% 7.58/2.58  
% 7.58/2.58  %Foreground sorts:
% 7.58/2.58  
% 7.58/2.58  
% 7.58/2.58  %Background operators:
% 7.58/2.58  
% 7.58/2.58  
% 7.58/2.58  %Foreground operators:
% 7.58/2.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.58/2.58  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.58/2.58  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.58/2.58  tff('#skF_4', type, '#skF_4': $i > $i).
% 7.58/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.58/2.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.58/2.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.58/2.58  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 7.58/2.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.58/2.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.58/2.58  tff('#skF_5', type, '#skF_5': $i).
% 7.58/2.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.58/2.58  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 7.58/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.58/2.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.58/2.58  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 7.58/2.58  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.58/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.58/2.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.58/2.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.58/2.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.58/2.58  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.58/2.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.58/2.58  
% 7.94/2.59  tff(f_99, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow_1)).
% 7.94/2.59  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 7.94/2.59  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.94/2.59  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.94/2.59  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 7.94/2.59  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 7.94/2.59  tff(f_43, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 7.94/2.59  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 7.94/2.59  tff(f_89, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 7.94/2.59  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.94/2.59  tff(c_64, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.94/2.59  tff(c_66, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.94/2.59  tff(c_136, plain, (![A_52]: (m1_subset_1(u1_pre_topc(A_52), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_52)))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.94/2.59  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.94/2.59  tff(c_140, plain, (![A_52]: (r1_tarski(u1_pre_topc(A_52), k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_136, c_16])).
% 7.94/2.59  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.94/2.59  tff(c_56, plain, (![A_15]: (r2_hidden(u1_struct_0(A_15), u1_pre_topc(A_15)) | ~v2_pre_topc(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.94/2.59  tff(c_145, plain, (![C_54, B_55, A_56]: (r1_tarski(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r1_tarski(k3_tarski(A_56), B_55))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.94/2.59  tff(c_428, plain, (![A_92, B_93]: (r1_tarski(u1_struct_0(A_92), B_93) | ~r1_tarski(k3_tarski(u1_pre_topc(A_92)), B_93) | ~v2_pre_topc(A_92) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_56, c_145])).
% 7.94/2.59  tff(c_444, plain, (![A_94]: (r1_tarski(u1_struct_0(A_94), k3_tarski(u1_pre_topc(A_94))) | ~v2_pre_topc(A_94) | ~l1_pre_topc(A_94))), inference(resolution, [status(thm)], [c_10, c_428])).
% 7.94/2.59  tff(c_14, plain, (![A_9]: (k3_tarski(k1_zfmisc_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.94/2.59  tff(c_99, plain, (![A_42, B_43]: (r1_tarski(k3_tarski(A_42), k3_tarski(B_43)) | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.94/2.59  tff(c_116, plain, (![A_46, A_47]: (r1_tarski(k3_tarski(A_46), A_47) | ~r1_tarski(A_46, k1_zfmisc_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_99])).
% 7.94/2.59  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.94/2.59  tff(c_122, plain, (![A_46, A_47]: (k3_tarski(A_46)=A_47 | ~r1_tarski(A_47, k3_tarski(A_46)) | ~r1_tarski(A_46, k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_116, c_6])).
% 7.94/2.59  tff(c_842, plain, (![A_141]: (k3_tarski(u1_pre_topc(A_141))=u1_struct_0(A_141) | ~r1_tarski(u1_pre_topc(A_141), k1_zfmisc_1(u1_struct_0(A_141))) | ~v2_pre_topc(A_141) | ~l1_pre_topc(A_141))), inference(resolution, [status(thm)], [c_444, c_122])).
% 7.94/2.59  tff(c_846, plain, (![A_52]: (k3_tarski(u1_pre_topc(A_52))=u1_struct_0(A_52) | ~v2_pre_topc(A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_140, c_842])).
% 7.94/2.59  tff(c_847, plain, (![A_142]: (k3_tarski(u1_pre_topc(A_142))=u1_struct_0(A_142) | ~v2_pre_topc(A_142) | ~l1_pre_topc(A_142))), inference(resolution, [status(thm)], [c_140, c_842])).
% 7.94/2.59  tff(c_60, plain, (![A_30]: (k4_yellow_0(k2_yellow_1(A_30))=k3_tarski(A_30) | ~r2_hidden(k3_tarski(A_30), A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.94/2.59  tff(c_3694, plain, (![A_328]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_328)))=k3_tarski(u1_pre_topc(A_328)) | ~r2_hidden(u1_struct_0(A_328), u1_pre_topc(A_328)) | v1_xboole_0(u1_pre_topc(A_328)) | ~v2_pre_topc(A_328) | ~l1_pre_topc(A_328))), inference(superposition, [status(thm), theory('equality')], [c_847, c_60])).
% 7.94/2.59  tff(c_3699, plain, (![A_329]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_329)))=k3_tarski(u1_pre_topc(A_329)) | v1_xboole_0(u1_pre_topc(A_329)) | ~v2_pre_topc(A_329) | ~l1_pre_topc(A_329))), inference(resolution, [status(thm)], [c_56, c_3694])).
% 7.94/2.59  tff(c_62, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_5')))!=u1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.94/2.59  tff(c_3705, plain, (k3_tarski(u1_pre_topc('#skF_5'))!=u1_struct_0('#skF_5') | v1_xboole_0(u1_pre_topc('#skF_5')) | ~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3699, c_62])).
% 7.94/2.59  tff(c_3711, plain, (k3_tarski(u1_pre_topc('#skF_5'))!=u1_struct_0('#skF_5') | v1_xboole_0(u1_pre_topc('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_3705])).
% 7.94/2.59  tff(c_3713, plain, (k3_tarski(u1_pre_topc('#skF_5'))!=u1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_3711])).
% 7.94/2.59  tff(c_3716, plain, (~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_846, c_3713])).
% 7.94/2.59  tff(c_3720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_3716])).
% 7.94/2.59  tff(c_3721, plain, (v1_xboole_0(u1_pre_topc('#skF_5'))), inference(splitRight, [status(thm)], [c_3711])).
% 7.94/2.59  tff(c_130, plain, (![A_50]: (r2_hidden(u1_struct_0(A_50), u1_pre_topc(A_50)) | ~v2_pre_topc(A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.94/2.59  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.94/2.59  tff(c_134, plain, (![A_50]: (~v1_xboole_0(u1_pre_topc(A_50)) | ~v2_pre_topc(A_50) | ~l1_pre_topc(A_50))), inference(resolution, [status(thm)], [c_130, c_2])).
% 7.94/2.59  tff(c_3725, plain, (~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_3721, c_134])).
% 7.94/2.59  tff(c_3729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_3725])).
% 7.94/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/2.59  
% 7.94/2.59  Inference rules
% 7.94/2.59  ----------------------
% 7.94/2.59  #Ref     : 0
% 7.94/2.59  #Sup     : 870
% 7.94/2.59  #Fact    : 0
% 7.94/2.59  #Define  : 0
% 7.94/2.59  #Split   : 1
% 7.94/2.59  #Chain   : 0
% 7.94/2.59  #Close   : 0
% 7.94/2.59  
% 7.94/2.59  Ordering : KBO
% 7.94/2.59  
% 7.94/2.59  Simplification rules
% 7.94/2.59  ----------------------
% 7.94/2.59  #Subsume      : 63
% 7.94/2.59  #Demod        : 173
% 7.94/2.59  #Tautology    : 106
% 7.94/2.59  #SimpNegUnit  : 0
% 7.94/2.59  #BackRed      : 0
% 7.94/2.59  
% 7.94/2.59  #Partial instantiations: 0
% 7.94/2.59  #Strategies tried      : 1
% 7.94/2.59  
% 7.94/2.59  Timing (in seconds)
% 7.94/2.59  ----------------------
% 7.94/2.59  Preprocessing        : 0.31
% 7.94/2.59  Parsing              : 0.16
% 7.94/2.59  CNF conversion       : 0.02
% 7.94/2.59  Main loop            : 1.54
% 7.94/2.59  Inferencing          : 0.37
% 7.94/2.60  Reduction            : 0.27
% 7.94/2.60  Demodulation         : 0.17
% 7.94/2.60  BG Simplification    : 0.06
% 7.94/2.60  Subsumption          : 0.75
% 7.94/2.60  Abstraction          : 0.06
% 7.94/2.60  MUC search           : 0.00
% 7.94/2.60  Cooper               : 0.00
% 7.94/2.60  Total                : 1.87
% 7.94/2.60  Index Insertion      : 0.00
% 7.94/2.60  Index Deletion       : 0.00
% 7.94/2.60  Index Matching       : 0.00
% 7.94/2.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
