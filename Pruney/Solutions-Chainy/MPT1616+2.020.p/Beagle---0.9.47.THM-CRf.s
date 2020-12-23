%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:38 EST 2020

% Result     : Theorem 7.87s
% Output     : CNFRefutation 8.09s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 157 expanded)
%              Number of leaves         :   34 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  120 ( 380 expanded)
%              Number of equality atoms :   17 (  46 expanded)
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

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

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

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_45,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(c_66,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_68,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_158,plain,(
    ! [A_54] :
      ( m1_subset_1(u1_pre_topc(A_54),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_54))))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_162,plain,(
    ! [A_54] :
      ( r1_tarski(u1_pre_topc(A_54),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_158,c_18])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(A_7,k1_zfmisc_1(k3_tarski(A_7))) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    ! [A_16] :
      ( r2_hidden(u1_struct_0(A_16),u1_pre_topc(A_16))
      | ~ v2_pre_topc(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_163,plain,(
    ! [A_55,C_56,B_57] :
      ( m1_subset_1(A_55,C_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(C_56))
      | ~ r2_hidden(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_180,plain,(
    ! [A_60,B_61,A_62] :
      ( m1_subset_1(A_60,B_61)
      | ~ r2_hidden(A_60,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(resolution,[status(thm)],[c_20,c_163])).

tff(c_363,plain,(
    ! [A_88,B_89] :
      ( m1_subset_1(u1_struct_0(A_88),B_89)
      | ~ r1_tarski(u1_pre_topc(A_88),B_89)
      | ~ v2_pre_topc(A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_58,c_180])).

tff(c_396,plain,(
    ! [A_93] :
      ( m1_subset_1(u1_struct_0(A_93),k1_zfmisc_1(k3_tarski(u1_pre_topc(A_93))))
      | ~ v2_pre_topc(A_93)
      | ~ l1_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_12,c_363])).

tff(c_404,plain,(
    ! [A_94] :
      ( r1_tarski(u1_struct_0(A_94),k3_tarski(u1_pre_topc(A_94)))
      | ~ v2_pre_topc(A_94)
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_396,c_18])).

tff(c_16,plain,(
    ! [A_10] : k3_tarski(k1_zfmisc_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_109,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k3_tarski(A_44),k3_tarski(B_45))
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_132,plain,(
    ! [A_48,A_49] :
      ( r1_tarski(k3_tarski(A_48),A_49)
      | ~ r1_tarski(A_48,k1_zfmisc_1(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_109])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_138,plain,(
    ! [A_48,A_49] :
      ( k3_tarski(A_48) = A_49
      | ~ r1_tarski(A_49,k3_tarski(A_48))
      | ~ r1_tarski(A_48,k1_zfmisc_1(A_49)) ) ),
    inference(resolution,[status(thm)],[c_132,c_6])).

tff(c_964,plain,(
    ! [A_167] :
      ( k3_tarski(u1_pre_topc(A_167)) = u1_struct_0(A_167)
      | ~ r1_tarski(u1_pre_topc(A_167),k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ v2_pre_topc(A_167)
      | ~ l1_pre_topc(A_167) ) ),
    inference(resolution,[status(thm)],[c_404,c_138])).

tff(c_968,plain,(
    ! [A_54] :
      ( k3_tarski(u1_pre_topc(A_54)) = u1_struct_0(A_54)
      | ~ v2_pre_topc(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_162,c_964])).

tff(c_975,plain,(
    ! [A_169] :
      ( k3_tarski(u1_pre_topc(A_169)) = u1_struct_0(A_169)
      | ~ v2_pre_topc(A_169)
      | ~ l1_pre_topc(A_169) ) ),
    inference(resolution,[status(thm)],[c_162,c_964])).

tff(c_62,plain,(
    ! [A_31] :
      ( k4_yellow_0(k2_yellow_1(A_31)) = k3_tarski(A_31)
      | ~ r2_hidden(k3_tarski(A_31),A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3625,plain,(
    ! [A_371] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_371))) = k3_tarski(u1_pre_topc(A_371))
      | ~ r2_hidden(u1_struct_0(A_371),u1_pre_topc(A_371))
      | v1_xboole_0(u1_pre_topc(A_371))
      | ~ v2_pre_topc(A_371)
      | ~ l1_pre_topc(A_371) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_975,c_62])).

tff(c_3630,plain,(
    ! [A_372] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_372))) = k3_tarski(u1_pre_topc(A_372))
      | v1_xboole_0(u1_pre_topc(A_372))
      | ~ v2_pre_topc(A_372)
      | ~ l1_pre_topc(A_372) ) ),
    inference(resolution,[status(thm)],[c_58,c_3625])).

tff(c_64,plain,(
    k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_5'))) != u1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3636,plain,
    ( k3_tarski(u1_pre_topc('#skF_5')) != u1_struct_0('#skF_5')
    | v1_xboole_0(u1_pre_topc('#skF_5'))
    | ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3630,c_64])).

tff(c_3642,plain,
    ( k3_tarski(u1_pre_topc('#skF_5')) != u1_struct_0('#skF_5')
    | v1_xboole_0(u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_3636])).

tff(c_3644,plain,(
    k3_tarski(u1_pre_topc('#skF_5')) != u1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3642])).

tff(c_3647,plain,
    ( ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_968,c_3644])).

tff(c_3651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_3647])).

tff(c_3652,plain,(
    v1_xboole_0(u1_pre_topc('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3642])).

tff(c_139,plain,(
    ! [A_50] :
      ( r2_hidden(u1_struct_0(A_50),u1_pre_topc(A_50))
      | ~ v2_pre_topc(A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_143,plain,(
    ! [A_50] :
      ( ~ v1_xboole_0(u1_pre_topc(A_50))
      | ~ v2_pre_topc(A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(resolution,[status(thm)],[c_139,c_2])).

tff(c_3656,plain,
    ( ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_3652,c_143])).

tff(c_3660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_3656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.87/2.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.87/2.63  
% 7.87/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.87/2.63  %$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_2 > #skF_4 > #skF_1 > #skF_5 > #skF_3
% 7.87/2.63  
% 7.87/2.63  %Foreground sorts:
% 7.87/2.63  
% 7.87/2.63  
% 7.87/2.63  %Background operators:
% 7.87/2.63  
% 7.87/2.63  
% 7.87/2.63  %Foreground operators:
% 7.87/2.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.87/2.63  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.87/2.63  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.87/2.63  tff('#skF_4', type, '#skF_4': $i > $i).
% 7.87/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.87/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.87/2.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.87/2.63  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 7.87/2.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.87/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.87/2.63  tff('#skF_5', type, '#skF_5': $i).
% 7.87/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.87/2.63  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 7.87/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.87/2.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.87/2.63  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 7.87/2.63  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.87/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.87/2.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.87/2.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.87/2.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.87/2.63  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.87/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.87/2.63  
% 8.09/2.65  tff(f_101, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 8.09/2.65  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 8.09/2.65  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.09/2.65  tff(f_39, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 8.09/2.65  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 8.09/2.65  tff(f_55, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 8.09/2.65  tff(f_45, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 8.09/2.65  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 8.09/2.65  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.09/2.65  tff(f_91, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 8.09/2.65  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.09/2.65  tff(c_66, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.09/2.65  tff(c_68, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.09/2.65  tff(c_158, plain, (![A_54]: (m1_subset_1(u1_pre_topc(A_54), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_54)))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.09/2.65  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.09/2.65  tff(c_162, plain, (![A_54]: (r1_tarski(u1_pre_topc(A_54), k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_158, c_18])).
% 8.09/2.65  tff(c_12, plain, (![A_7]: (r1_tarski(A_7, k1_zfmisc_1(k3_tarski(A_7))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.09/2.65  tff(c_58, plain, (![A_16]: (r2_hidden(u1_struct_0(A_16), u1_pre_topc(A_16)) | ~v2_pre_topc(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.09/2.65  tff(c_20, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.09/2.65  tff(c_163, plain, (![A_55, C_56, B_57]: (m1_subset_1(A_55, C_56) | ~m1_subset_1(B_57, k1_zfmisc_1(C_56)) | ~r2_hidden(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.09/2.65  tff(c_180, plain, (![A_60, B_61, A_62]: (m1_subset_1(A_60, B_61) | ~r2_hidden(A_60, A_62) | ~r1_tarski(A_62, B_61))), inference(resolution, [status(thm)], [c_20, c_163])).
% 8.09/2.65  tff(c_363, plain, (![A_88, B_89]: (m1_subset_1(u1_struct_0(A_88), B_89) | ~r1_tarski(u1_pre_topc(A_88), B_89) | ~v2_pre_topc(A_88) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_58, c_180])).
% 8.09/2.65  tff(c_396, plain, (![A_93]: (m1_subset_1(u1_struct_0(A_93), k1_zfmisc_1(k3_tarski(u1_pre_topc(A_93)))) | ~v2_pre_topc(A_93) | ~l1_pre_topc(A_93))), inference(resolution, [status(thm)], [c_12, c_363])).
% 8.09/2.65  tff(c_404, plain, (![A_94]: (r1_tarski(u1_struct_0(A_94), k3_tarski(u1_pre_topc(A_94))) | ~v2_pre_topc(A_94) | ~l1_pre_topc(A_94))), inference(resolution, [status(thm)], [c_396, c_18])).
% 8.09/2.65  tff(c_16, plain, (![A_10]: (k3_tarski(k1_zfmisc_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.09/2.65  tff(c_109, plain, (![A_44, B_45]: (r1_tarski(k3_tarski(A_44), k3_tarski(B_45)) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.09/2.65  tff(c_132, plain, (![A_48, A_49]: (r1_tarski(k3_tarski(A_48), A_49) | ~r1_tarski(A_48, k1_zfmisc_1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_109])).
% 8.09/2.65  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.09/2.65  tff(c_138, plain, (![A_48, A_49]: (k3_tarski(A_48)=A_49 | ~r1_tarski(A_49, k3_tarski(A_48)) | ~r1_tarski(A_48, k1_zfmisc_1(A_49)))), inference(resolution, [status(thm)], [c_132, c_6])).
% 8.09/2.65  tff(c_964, plain, (![A_167]: (k3_tarski(u1_pre_topc(A_167))=u1_struct_0(A_167) | ~r1_tarski(u1_pre_topc(A_167), k1_zfmisc_1(u1_struct_0(A_167))) | ~v2_pre_topc(A_167) | ~l1_pre_topc(A_167))), inference(resolution, [status(thm)], [c_404, c_138])).
% 8.09/2.65  tff(c_968, plain, (![A_54]: (k3_tarski(u1_pre_topc(A_54))=u1_struct_0(A_54) | ~v2_pre_topc(A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_162, c_964])).
% 8.09/2.65  tff(c_975, plain, (![A_169]: (k3_tarski(u1_pre_topc(A_169))=u1_struct_0(A_169) | ~v2_pre_topc(A_169) | ~l1_pre_topc(A_169))), inference(resolution, [status(thm)], [c_162, c_964])).
% 8.09/2.65  tff(c_62, plain, (![A_31]: (k4_yellow_0(k2_yellow_1(A_31))=k3_tarski(A_31) | ~r2_hidden(k3_tarski(A_31), A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.09/2.65  tff(c_3625, plain, (![A_371]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_371)))=k3_tarski(u1_pre_topc(A_371)) | ~r2_hidden(u1_struct_0(A_371), u1_pre_topc(A_371)) | v1_xboole_0(u1_pre_topc(A_371)) | ~v2_pre_topc(A_371) | ~l1_pre_topc(A_371))), inference(superposition, [status(thm), theory('equality')], [c_975, c_62])).
% 8.09/2.65  tff(c_3630, plain, (![A_372]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_372)))=k3_tarski(u1_pre_topc(A_372)) | v1_xboole_0(u1_pre_topc(A_372)) | ~v2_pre_topc(A_372) | ~l1_pre_topc(A_372))), inference(resolution, [status(thm)], [c_58, c_3625])).
% 8.09/2.65  tff(c_64, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_5')))!=u1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.09/2.65  tff(c_3636, plain, (k3_tarski(u1_pre_topc('#skF_5'))!=u1_struct_0('#skF_5') | v1_xboole_0(u1_pre_topc('#skF_5')) | ~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3630, c_64])).
% 8.09/2.65  tff(c_3642, plain, (k3_tarski(u1_pre_topc('#skF_5'))!=u1_struct_0('#skF_5') | v1_xboole_0(u1_pre_topc('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_3636])).
% 8.09/2.65  tff(c_3644, plain, (k3_tarski(u1_pre_topc('#skF_5'))!=u1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_3642])).
% 8.09/2.65  tff(c_3647, plain, (~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_968, c_3644])).
% 8.09/2.65  tff(c_3651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_3647])).
% 8.09/2.65  tff(c_3652, plain, (v1_xboole_0(u1_pre_topc('#skF_5'))), inference(splitRight, [status(thm)], [c_3642])).
% 8.09/2.65  tff(c_139, plain, (![A_50]: (r2_hidden(u1_struct_0(A_50), u1_pre_topc(A_50)) | ~v2_pre_topc(A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.09/2.65  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.09/2.65  tff(c_143, plain, (![A_50]: (~v1_xboole_0(u1_pre_topc(A_50)) | ~v2_pre_topc(A_50) | ~l1_pre_topc(A_50))), inference(resolution, [status(thm)], [c_139, c_2])).
% 8.09/2.65  tff(c_3656, plain, (~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_3652, c_143])).
% 8.09/2.65  tff(c_3660, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_3656])).
% 8.09/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.09/2.65  
% 8.09/2.65  Inference rules
% 8.09/2.65  ----------------------
% 8.09/2.65  #Ref     : 0
% 8.09/2.65  #Sup     : 881
% 8.09/2.65  #Fact    : 2
% 8.09/2.65  #Define  : 0
% 8.09/2.65  #Split   : 1
% 8.09/2.65  #Chain   : 0
% 8.09/2.65  #Close   : 0
% 8.09/2.65  
% 8.09/2.65  Ordering : KBO
% 8.09/2.65  
% 8.09/2.65  Simplification rules
% 8.09/2.65  ----------------------
% 8.09/2.65  #Subsume      : 86
% 8.09/2.65  #Demod        : 314
% 8.09/2.65  #Tautology    : 170
% 8.09/2.65  #SimpNegUnit  : 0
% 8.09/2.65  #BackRed      : 0
% 8.09/2.65  
% 8.09/2.65  #Partial instantiations: 0
% 8.09/2.65  #Strategies tried      : 1
% 8.09/2.65  
% 8.09/2.65  Timing (in seconds)
% 8.09/2.65  ----------------------
% 8.09/2.65  Preprocessing        : 0.32
% 8.09/2.65  Parsing              : 0.17
% 8.09/2.65  CNF conversion       : 0.02
% 8.09/2.65  Main loop            : 1.58
% 8.11/2.65  Inferencing          : 0.37
% 8.11/2.65  Reduction            : 0.30
% 8.11/2.65  Demodulation         : 0.19
% 8.11/2.65  BG Simplification    : 0.05
% 8.11/2.65  Subsumption          : 0.77
% 8.11/2.65  Abstraction          : 0.06
% 8.11/2.65  MUC search           : 0.00
% 8.11/2.65  Cooper               : 0.00
% 8.11/2.65  Total                : 1.92
% 8.11/2.65  Index Insertion      : 0.00
% 8.11/2.65  Index Deletion       : 0.00
% 8.11/2.65  Index Matching       : 0.00
% 8.11/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
