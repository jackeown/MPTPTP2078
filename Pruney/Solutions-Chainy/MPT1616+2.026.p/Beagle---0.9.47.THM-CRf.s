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

% Result     : Theorem 9.89s
% Output     : CNFRefutation 9.95s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 135 expanded)
%              Number of leaves         :   32 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  112 ( 328 expanded)
%              Number of equality atoms :   18 (  50 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

tff(f_77,axiom,(
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

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_62,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_54,plain,(
    ! [A_13] :
      ( r2_hidden(u1_struct_0(A_13),u1_pre_topc(A_13))
      | ~ v2_pre_topc(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_136,plain,(
    ! [A_50] :
      ( m1_subset_1(u1_pre_topc(A_50),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_50))))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_140,plain,(
    ! [A_50] :
      ( r1_tarski(u1_pre_topc(A_50),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(resolution,[status(thm)],[c_136,c_14])).

tff(c_12,plain,(
    ! [A_7] : k3_tarski(k1_zfmisc_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(k3_tarski(A_41),k3_tarski(B_42))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_107,plain,(
    ! [A_41,A_7] :
      ( r1_tarski(k3_tarski(A_41),A_7)
      | ~ r1_tarski(A_41,k1_zfmisc_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_99])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,k3_tarski(B_4))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_88,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(B_37,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_174,plain,(
    ! [B_63,A_64] :
      ( k3_tarski(B_63) = A_64
      | ~ r1_tarski(k3_tarski(B_63),A_64)
      | ~ r2_hidden(A_64,B_63) ) ),
    inference(resolution,[status(thm)],[c_8,c_88])).

tff(c_237,plain,(
    ! [A_75,A_76] :
      ( k3_tarski(A_75) = A_76
      | ~ r2_hidden(A_76,A_75)
      | ~ r1_tarski(A_75,k1_zfmisc_1(A_76)) ) ),
    inference(resolution,[status(thm)],[c_107,c_174])).

tff(c_514,plain,(
    ! [A_112] :
      ( k3_tarski(u1_pre_topc(A_112)) = u1_struct_0(A_112)
      | ~ r2_hidden(u1_struct_0(A_112),u1_pre_topc(A_112))
      | ~ l1_pre_topc(A_112) ) ),
    inference(resolution,[status(thm)],[c_140,c_237])).

tff(c_518,plain,(
    ! [A_13] :
      ( k3_tarski(u1_pre_topc(A_13)) = u1_struct_0(A_13)
      | ~ v2_pre_topc(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(resolution,[status(thm)],[c_54,c_514])).

tff(c_519,plain,(
    ! [A_113] :
      ( k3_tarski(u1_pre_topc(A_113)) = u1_struct_0(A_113)
      | ~ v2_pre_topc(A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_54,c_514])).

tff(c_58,plain,(
    ! [A_28] :
      ( k4_yellow_0(k2_yellow_1(A_28)) = k3_tarski(A_28)
      | ~ r2_hidden(k3_tarski(A_28),A_28)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5891,plain,(
    ! [A_586] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_586))) = k3_tarski(u1_pre_topc(A_586))
      | ~ r2_hidden(u1_struct_0(A_586),u1_pre_topc(A_586))
      | v1_xboole_0(u1_pre_topc(A_586))
      | ~ v2_pre_topc(A_586)
      | ~ l1_pre_topc(A_586) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_58])).

tff(c_5896,plain,(
    ! [A_587] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_587))) = k3_tarski(u1_pre_topc(A_587))
      | v1_xboole_0(u1_pre_topc(A_587))
      | ~ v2_pre_topc(A_587)
      | ~ l1_pre_topc(A_587) ) ),
    inference(resolution,[status(thm)],[c_54,c_5891])).

tff(c_60,plain,(
    k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_4'))) != u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5902,plain,
    ( k3_tarski(u1_pre_topc('#skF_4')) != u1_struct_0('#skF_4')
    | v1_xboole_0(u1_pre_topc('#skF_4'))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5896,c_60])).

tff(c_5908,plain,
    ( k3_tarski(u1_pre_topc('#skF_4')) != u1_struct_0('#skF_4')
    | v1_xboole_0(u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_5902])).

tff(c_5910,plain,(
    k3_tarski(u1_pre_topc('#skF_4')) != u1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5908])).

tff(c_5913,plain,
    ( ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_5910])).

tff(c_5917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_5913])).

tff(c_5918,plain,(
    v1_xboole_0(u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5908])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_145,plain,(
    ! [C_52,B_53,A_54] :
      ( ~ v1_xboole_0(C_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(C_52))
      | ~ r2_hidden(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_157,plain,(
    ! [B_56,A_57,A_58] :
      ( ~ v1_xboole_0(B_56)
      | ~ r2_hidden(A_57,A_58)
      | ~ r1_tarski(A_58,B_56) ) ),
    inference(resolution,[status(thm)],[c_16,c_145])).

tff(c_210,plain,(
    ! [B_70,A_71] :
      ( ~ v1_xboole_0(B_70)
      | ~ r1_tarski(u1_pre_topc(A_71),B_70)
      | ~ v2_pre_topc(A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_54,c_157])).

tff(c_229,plain,(
    ! [A_71] :
      ( ~ v1_xboole_0(u1_pre_topc(A_71))
      | ~ v2_pre_topc(A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_210])).

tff(c_5922,plain,
    ( ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_5918,c_229])).

tff(c_5926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_5922])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.89/3.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.89/3.59  
% 9.89/3.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.89/3.59  %$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 9.89/3.59  
% 9.89/3.59  %Foreground sorts:
% 9.89/3.59  
% 9.89/3.59  
% 9.89/3.59  %Background operators:
% 9.89/3.59  
% 9.89/3.59  
% 9.89/3.59  %Foreground operators:
% 9.89/3.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.89/3.59  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 9.89/3.59  tff('#skF_2', type, '#skF_2': $i > $i).
% 9.89/3.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.89/3.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.89/3.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.89/3.59  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 9.89/3.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.89/3.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.89/3.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.89/3.59  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 9.89/3.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.89/3.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.89/3.59  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 9.89/3.59  tff('#skF_4', type, '#skF_4': $i).
% 9.89/3.59  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.89/3.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.89/3.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.89/3.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.89/3.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.89/3.59  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.89/3.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.89/3.59  
% 9.95/3.60  tff(f_98, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow_1)).
% 9.95/3.60  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 9.95/3.60  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 9.95/3.60  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.95/3.60  tff(f_41, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 9.95/3.60  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 9.95/3.60  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 9.95/3.60  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.95/3.60  tff(f_88, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 9.95/3.60  tff(f_52, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 9.95/3.60  tff(c_62, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.95/3.60  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.95/3.60  tff(c_54, plain, (![A_13]: (r2_hidden(u1_struct_0(A_13), u1_pre_topc(A_13)) | ~v2_pre_topc(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.95/3.60  tff(c_136, plain, (![A_50]: (m1_subset_1(u1_pre_topc(A_50), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_50)))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.95/3.60  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.95/3.60  tff(c_140, plain, (![A_50]: (r1_tarski(u1_pre_topc(A_50), k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(resolution, [status(thm)], [c_136, c_14])).
% 9.95/3.60  tff(c_12, plain, (![A_7]: (k3_tarski(k1_zfmisc_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.95/3.60  tff(c_99, plain, (![A_41, B_42]: (r1_tarski(k3_tarski(A_41), k3_tarski(B_42)) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.95/3.60  tff(c_107, plain, (![A_41, A_7]: (r1_tarski(k3_tarski(A_41), A_7) | ~r1_tarski(A_41, k1_zfmisc_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_99])).
% 9.95/3.60  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, k3_tarski(B_4)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.95/3.60  tff(c_88, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(B_37, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.95/3.60  tff(c_174, plain, (![B_63, A_64]: (k3_tarski(B_63)=A_64 | ~r1_tarski(k3_tarski(B_63), A_64) | ~r2_hidden(A_64, B_63))), inference(resolution, [status(thm)], [c_8, c_88])).
% 9.95/3.60  tff(c_237, plain, (![A_75, A_76]: (k3_tarski(A_75)=A_76 | ~r2_hidden(A_76, A_75) | ~r1_tarski(A_75, k1_zfmisc_1(A_76)))), inference(resolution, [status(thm)], [c_107, c_174])).
% 9.95/3.60  tff(c_514, plain, (![A_112]: (k3_tarski(u1_pre_topc(A_112))=u1_struct_0(A_112) | ~r2_hidden(u1_struct_0(A_112), u1_pre_topc(A_112)) | ~l1_pre_topc(A_112))), inference(resolution, [status(thm)], [c_140, c_237])).
% 9.95/3.60  tff(c_518, plain, (![A_13]: (k3_tarski(u1_pre_topc(A_13))=u1_struct_0(A_13) | ~v2_pre_topc(A_13) | ~l1_pre_topc(A_13))), inference(resolution, [status(thm)], [c_54, c_514])).
% 9.95/3.60  tff(c_519, plain, (![A_113]: (k3_tarski(u1_pre_topc(A_113))=u1_struct_0(A_113) | ~v2_pre_topc(A_113) | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_54, c_514])).
% 9.95/3.60  tff(c_58, plain, (![A_28]: (k4_yellow_0(k2_yellow_1(A_28))=k3_tarski(A_28) | ~r2_hidden(k3_tarski(A_28), A_28) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.95/3.60  tff(c_5891, plain, (![A_586]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_586)))=k3_tarski(u1_pre_topc(A_586)) | ~r2_hidden(u1_struct_0(A_586), u1_pre_topc(A_586)) | v1_xboole_0(u1_pre_topc(A_586)) | ~v2_pre_topc(A_586) | ~l1_pre_topc(A_586))), inference(superposition, [status(thm), theory('equality')], [c_519, c_58])).
% 9.95/3.60  tff(c_5896, plain, (![A_587]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_587)))=k3_tarski(u1_pre_topc(A_587)) | v1_xboole_0(u1_pre_topc(A_587)) | ~v2_pre_topc(A_587) | ~l1_pre_topc(A_587))), inference(resolution, [status(thm)], [c_54, c_5891])).
% 9.95/3.60  tff(c_60, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_4')))!=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.95/3.60  tff(c_5902, plain, (k3_tarski(u1_pre_topc('#skF_4'))!=u1_struct_0('#skF_4') | v1_xboole_0(u1_pre_topc('#skF_4')) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5896, c_60])).
% 9.95/3.60  tff(c_5908, plain, (k3_tarski(u1_pre_topc('#skF_4'))!=u1_struct_0('#skF_4') | v1_xboole_0(u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_64, c_5902])).
% 9.95/3.60  tff(c_5910, plain, (k3_tarski(u1_pre_topc('#skF_4'))!=u1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_5908])).
% 9.95/3.60  tff(c_5913, plain, (~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_518, c_5910])).
% 9.95/3.60  tff(c_5917, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_64, c_5913])).
% 9.95/3.60  tff(c_5918, plain, (v1_xboole_0(u1_pre_topc('#skF_4'))), inference(splitRight, [status(thm)], [c_5908])).
% 9.95/3.60  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.95/3.60  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.95/3.60  tff(c_145, plain, (![C_52, B_53, A_54]: (~v1_xboole_0(C_52) | ~m1_subset_1(B_53, k1_zfmisc_1(C_52)) | ~r2_hidden(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.95/3.60  tff(c_157, plain, (![B_56, A_57, A_58]: (~v1_xboole_0(B_56) | ~r2_hidden(A_57, A_58) | ~r1_tarski(A_58, B_56))), inference(resolution, [status(thm)], [c_16, c_145])).
% 9.95/3.60  tff(c_210, plain, (![B_70, A_71]: (~v1_xboole_0(B_70) | ~r1_tarski(u1_pre_topc(A_71), B_70) | ~v2_pre_topc(A_71) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_54, c_157])).
% 9.95/3.60  tff(c_229, plain, (![A_71]: (~v1_xboole_0(u1_pre_topc(A_71)) | ~v2_pre_topc(A_71) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_6, c_210])).
% 9.95/3.60  tff(c_5922, plain, (~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_5918, c_229])).
% 9.95/3.60  tff(c_5926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_64, c_5922])).
% 9.95/3.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.95/3.60  
% 9.95/3.60  Inference rules
% 9.95/3.60  ----------------------
% 9.95/3.60  #Ref     : 0
% 9.95/3.60  #Sup     : 1535
% 9.95/3.60  #Fact    : 0
% 9.95/3.60  #Define  : 0
% 9.95/3.60  #Split   : 1
% 9.95/3.60  #Chain   : 0
% 9.95/3.60  #Close   : 0
% 9.95/3.60  
% 9.95/3.61  Ordering : KBO
% 9.95/3.61  
% 9.95/3.61  Simplification rules
% 9.95/3.61  ----------------------
% 9.95/3.61  #Subsume      : 133
% 9.95/3.61  #Demod        : 276
% 9.95/3.61  #Tautology    : 144
% 9.95/3.61  #SimpNegUnit  : 0
% 9.95/3.61  #BackRed      : 0
% 9.95/3.61  
% 9.95/3.61  #Partial instantiations: 0
% 9.95/3.61  #Strategies tried      : 1
% 9.95/3.61  
% 9.95/3.61  Timing (in seconds)
% 9.95/3.61  ----------------------
% 9.95/3.61  Preprocessing        : 0.32
% 9.95/3.61  Parsing              : 0.18
% 9.95/3.61  CNF conversion       : 0.02
% 9.95/3.61  Main loop            : 2.49
% 9.95/3.61  Inferencing          : 0.47
% 9.95/3.61  Reduction            : 0.36
% 9.95/3.61  Demodulation         : 0.23
% 9.95/3.61  BG Simplification    : 0.07
% 10.03/3.61  Subsumption          : 1.47
% 10.03/3.61  Abstraction          : 0.07
% 10.03/3.61  MUC search           : 0.00
% 10.03/3.61  Cooper               : 0.00
% 10.03/3.61  Total                : 2.85
% 10.03/3.61  Index Insertion      : 0.00
% 10.03/3.61  Index Deletion       : 0.00
% 10.03/3.61  Index Matching       : 0.00
% 10.03/3.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
