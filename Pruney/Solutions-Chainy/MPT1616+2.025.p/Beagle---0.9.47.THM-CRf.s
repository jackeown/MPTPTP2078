%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:38 EST 2020

% Result     : Theorem 11.04s
% Output     : CNFRefutation 11.17s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 110 expanded)
%              Number of leaves         :   35 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 244 expanded)
%              Number of equality atoms :   19 (  39 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

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

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

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

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_53,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_120,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ~ v1_xboole_0(u1_pre_topc(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_pre_topc)).

tff(c_76,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_74,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_56,plain,(
    ! [A_14] :
      ( r2_hidden(u1_struct_0(A_14),u1_pre_topc(A_14))
      | ~ v2_pre_topc(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_135,plain,(
    ! [A_56] :
      ( m1_subset_1(u1_pre_topc(A_56),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56))))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_139,plain,(
    ! [A_56] :
      ( r1_tarski(u1_pre_topc(A_56),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_135,c_18])).

tff(c_12,plain,(
    ! [A_7] : k3_tarski(k1_zfmisc_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_113,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k3_tarski(A_52),k3_tarski(B_53))
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_121,plain,(
    ! [A_52,A_7] :
      ( r1_tarski(k3_tarski(A_52),A_7)
      | ~ r1_tarski(A_52,k1_zfmisc_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_113])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,k3_tarski(B_4))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_103,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(B_50,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_212,plain,(
    ! [B_73,A_74] :
      ( k3_tarski(B_73) = A_74
      | ~ r1_tarski(k3_tarski(B_73),A_74)
      | ~ r2_hidden(A_74,B_73) ) ),
    inference(resolution,[status(thm)],[c_8,c_103])).

tff(c_296,plain,(
    ! [A_84,A_85] :
      ( k3_tarski(A_84) = A_85
      | ~ r2_hidden(A_85,A_84)
      | ~ r1_tarski(A_84,k1_zfmisc_1(A_85)) ) ),
    inference(resolution,[status(thm)],[c_121,c_212])).

tff(c_710,plain,(
    ! [A_133] :
      ( k3_tarski(u1_pre_topc(A_133)) = u1_struct_0(A_133)
      | ~ r2_hidden(u1_struct_0(A_133),u1_pre_topc(A_133))
      | ~ l1_pre_topc(A_133) ) ),
    inference(resolution,[status(thm)],[c_139,c_296])).

tff(c_718,plain,(
    ! [A_14] :
      ( k3_tarski(u1_pre_topc(A_14)) = u1_struct_0(A_14)
      | ~ v2_pre_topc(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(resolution,[status(thm)],[c_56,c_710])).

tff(c_62,plain,(
    ! [A_31] :
      ( m1_subset_1(u1_pre_topc(A_31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_31))))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_172,plain,(
    ! [A_67,B_68] :
      ( k5_setfam_1(A_67,B_68) = k3_tarski(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_180,plain,(
    ! [A_31] :
      ( k5_setfam_1(u1_struct_0(A_31),u1_pre_topc(A_31)) = k3_tarski(u1_pre_topc(A_31))
      | ~ l1_pre_topc(A_31) ) ),
    inference(resolution,[status(thm)],[c_62,c_172])).

tff(c_934,plain,(
    ! [A_148,B_149] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_148),B_149),u1_pre_topc(A_148))
      | ~ r1_tarski(B_149,u1_pre_topc(A_148))
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_148))))
      | ~ v2_pre_topc(A_148)
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_940,plain,(
    ! [A_31] :
      ( r2_hidden(k3_tarski(u1_pre_topc(A_31)),u1_pre_topc(A_31))
      | ~ r1_tarski(u1_pre_topc(A_31),u1_pre_topc(A_31))
      | ~ m1_subset_1(u1_pre_topc(A_31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_31))))
      | ~ v2_pre_topc(A_31)
      | ~ l1_pre_topc(A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_934])).

tff(c_3961,plain,(
    ! [A_396] :
      ( r2_hidden(k3_tarski(u1_pre_topc(A_396)),u1_pre_topc(A_396))
      | ~ m1_subset_1(u1_pre_topc(A_396),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_396))))
      | ~ v2_pre_topc(A_396)
      | ~ l1_pre_topc(A_396) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_940])).

tff(c_3970,plain,(
    ! [A_397] :
      ( r2_hidden(k3_tarski(u1_pre_topc(A_397)),u1_pre_topc(A_397))
      | ~ v2_pre_topc(A_397)
      | ~ l1_pre_topc(A_397) ) ),
    inference(resolution,[status(thm)],[c_62,c_3961])).

tff(c_70,plain,(
    ! [A_37] :
      ( k4_yellow_0(k2_yellow_1(A_37)) = k3_tarski(A_37)
      | ~ r2_hidden(k3_tarski(A_37),A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4023,plain,(
    ! [A_398] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_398))) = k3_tarski(u1_pre_topc(A_398))
      | v1_xboole_0(u1_pre_topc(A_398))
      | ~ v2_pre_topc(A_398)
      | ~ l1_pre_topc(A_398) ) ),
    inference(resolution,[status(thm)],[c_3970,c_70])).

tff(c_72,plain,(
    k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_4'))) != u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4029,plain,
    ( k3_tarski(u1_pre_topc('#skF_4')) != u1_struct_0('#skF_4')
    | v1_xboole_0(u1_pre_topc('#skF_4'))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4023,c_72])).

tff(c_4035,plain,
    ( k3_tarski(u1_pre_topc('#skF_4')) != u1_struct_0('#skF_4')
    | v1_xboole_0(u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_4029])).

tff(c_4037,plain,(
    k3_tarski(u1_pre_topc('#skF_4')) != u1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4035])).

tff(c_4040,plain,
    ( ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_718,c_4037])).

tff(c_4044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_4040])).

tff(c_4045,plain,(
    v1_xboole_0(u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4035])).

tff(c_64,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(u1_pre_topc(A_32))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4065,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4045,c_64])).

tff(c_4069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_4065])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:50:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.04/3.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.14/3.71  
% 11.14/3.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.14/3.72  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 11.14/3.72  
% 11.14/3.72  %Foreground sorts:
% 11.14/3.72  
% 11.14/3.72  
% 11.14/3.72  %Background operators:
% 11.14/3.72  
% 11.14/3.72  
% 11.14/3.72  %Foreground operators:
% 11.14/3.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.14/3.72  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 11.14/3.72  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 11.14/3.72  tff('#skF_2', type, '#skF_2': $i > $i).
% 11.14/3.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.14/3.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.14/3.72  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.14/3.72  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 11.14/3.72  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 11.14/3.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.14/3.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.14/3.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.14/3.72  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 11.14/3.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.14/3.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.14/3.72  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 11.14/3.72  tff('#skF_4', type, '#skF_4': $i).
% 11.14/3.72  tff('#skF_3', type, '#skF_3': $i > $i).
% 11.14/3.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.14/3.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.14/3.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.14/3.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.14/3.72  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 11.14/3.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.14/3.72  
% 11.17/3.74  tff(f_130, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow_1)).
% 11.17/3.74  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 11.17/3.74  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 11.17/3.74  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.17/3.74  tff(f_41, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 11.17/3.74  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 11.17/3.74  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 11.17/3.74  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.17/3.74  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 11.17/3.74  tff(f_120, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 11.17/3.74  tff(f_98, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => ~v1_xboole_0(u1_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_pre_topc)).
% 11.17/3.74  tff(c_76, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.17/3.74  tff(c_74, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.17/3.74  tff(c_56, plain, (![A_14]: (r2_hidden(u1_struct_0(A_14), u1_pre_topc(A_14)) | ~v2_pre_topc(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.17/3.74  tff(c_135, plain, (![A_56]: (m1_subset_1(u1_pre_topc(A_56), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56)))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.17/3.74  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.17/3.74  tff(c_139, plain, (![A_56]: (r1_tarski(u1_pre_topc(A_56), k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_135, c_18])).
% 11.17/3.74  tff(c_12, plain, (![A_7]: (k3_tarski(k1_zfmisc_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.17/3.74  tff(c_113, plain, (![A_52, B_53]: (r1_tarski(k3_tarski(A_52), k3_tarski(B_53)) | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.17/3.74  tff(c_121, plain, (![A_52, A_7]: (r1_tarski(k3_tarski(A_52), A_7) | ~r1_tarski(A_52, k1_zfmisc_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_113])).
% 11.17/3.74  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, k3_tarski(B_4)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.17/3.74  tff(c_103, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(B_50, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.17/3.74  tff(c_212, plain, (![B_73, A_74]: (k3_tarski(B_73)=A_74 | ~r1_tarski(k3_tarski(B_73), A_74) | ~r2_hidden(A_74, B_73))), inference(resolution, [status(thm)], [c_8, c_103])).
% 11.17/3.74  tff(c_296, plain, (![A_84, A_85]: (k3_tarski(A_84)=A_85 | ~r2_hidden(A_85, A_84) | ~r1_tarski(A_84, k1_zfmisc_1(A_85)))), inference(resolution, [status(thm)], [c_121, c_212])).
% 11.17/3.74  tff(c_710, plain, (![A_133]: (k3_tarski(u1_pre_topc(A_133))=u1_struct_0(A_133) | ~r2_hidden(u1_struct_0(A_133), u1_pre_topc(A_133)) | ~l1_pre_topc(A_133))), inference(resolution, [status(thm)], [c_139, c_296])).
% 11.17/3.74  tff(c_718, plain, (![A_14]: (k3_tarski(u1_pre_topc(A_14))=u1_struct_0(A_14) | ~v2_pre_topc(A_14) | ~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_56, c_710])).
% 11.17/3.74  tff(c_62, plain, (![A_31]: (m1_subset_1(u1_pre_topc(A_31), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_31)))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.17/3.74  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.17/3.74  tff(c_172, plain, (![A_67, B_68]: (k5_setfam_1(A_67, B_68)=k3_tarski(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(k1_zfmisc_1(A_67))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.17/3.74  tff(c_180, plain, (![A_31]: (k5_setfam_1(u1_struct_0(A_31), u1_pre_topc(A_31))=k3_tarski(u1_pre_topc(A_31)) | ~l1_pre_topc(A_31))), inference(resolution, [status(thm)], [c_62, c_172])).
% 11.17/3.74  tff(c_934, plain, (![A_148, B_149]: (r2_hidden(k5_setfam_1(u1_struct_0(A_148), B_149), u1_pre_topc(A_148)) | ~r1_tarski(B_149, u1_pre_topc(A_148)) | ~m1_subset_1(B_149, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_148)))) | ~v2_pre_topc(A_148) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.17/3.74  tff(c_940, plain, (![A_31]: (r2_hidden(k3_tarski(u1_pre_topc(A_31)), u1_pre_topc(A_31)) | ~r1_tarski(u1_pre_topc(A_31), u1_pre_topc(A_31)) | ~m1_subset_1(u1_pre_topc(A_31), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_31)))) | ~v2_pre_topc(A_31) | ~l1_pre_topc(A_31) | ~l1_pre_topc(A_31))), inference(superposition, [status(thm), theory('equality')], [c_180, c_934])).
% 11.17/3.74  tff(c_3961, plain, (![A_396]: (r2_hidden(k3_tarski(u1_pre_topc(A_396)), u1_pre_topc(A_396)) | ~m1_subset_1(u1_pre_topc(A_396), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_396)))) | ~v2_pre_topc(A_396) | ~l1_pre_topc(A_396))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_940])).
% 11.17/3.74  tff(c_3970, plain, (![A_397]: (r2_hidden(k3_tarski(u1_pre_topc(A_397)), u1_pre_topc(A_397)) | ~v2_pre_topc(A_397) | ~l1_pre_topc(A_397))), inference(resolution, [status(thm)], [c_62, c_3961])).
% 11.17/3.74  tff(c_70, plain, (![A_37]: (k4_yellow_0(k2_yellow_1(A_37))=k3_tarski(A_37) | ~r2_hidden(k3_tarski(A_37), A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.17/3.74  tff(c_4023, plain, (![A_398]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_398)))=k3_tarski(u1_pre_topc(A_398)) | v1_xboole_0(u1_pre_topc(A_398)) | ~v2_pre_topc(A_398) | ~l1_pre_topc(A_398))), inference(resolution, [status(thm)], [c_3970, c_70])).
% 11.17/3.74  tff(c_72, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_4')))!=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.17/3.74  tff(c_4029, plain, (k3_tarski(u1_pre_topc('#skF_4'))!=u1_struct_0('#skF_4') | v1_xboole_0(u1_pre_topc('#skF_4')) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4023, c_72])).
% 11.17/3.74  tff(c_4035, plain, (k3_tarski(u1_pre_topc('#skF_4'))!=u1_struct_0('#skF_4') | v1_xboole_0(u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_4029])).
% 11.17/3.74  tff(c_4037, plain, (k3_tarski(u1_pre_topc('#skF_4'))!=u1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_4035])).
% 11.17/3.74  tff(c_4040, plain, (~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_718, c_4037])).
% 11.17/3.74  tff(c_4044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_4040])).
% 11.17/3.74  tff(c_4045, plain, (v1_xboole_0(u1_pre_topc('#skF_4'))), inference(splitRight, [status(thm)], [c_4035])).
% 11.17/3.74  tff(c_64, plain, (![A_32]: (~v1_xboole_0(u1_pre_topc(A_32)) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.17/3.74  tff(c_4065, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4045, c_64])).
% 11.17/3.74  tff(c_4069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_4065])).
% 11.17/3.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.17/3.74  
% 11.17/3.74  Inference rules
% 11.17/3.74  ----------------------
% 11.17/3.74  #Ref     : 0
% 11.17/3.74  #Sup     : 966
% 11.17/3.74  #Fact    : 0
% 11.17/3.74  #Define  : 0
% 11.17/3.74  #Split   : 1
% 11.17/3.74  #Chain   : 0
% 11.17/3.74  #Close   : 0
% 11.17/3.74  
% 11.17/3.74  Ordering : KBO
% 11.17/3.74  
% 11.17/3.74  Simplification rules
% 11.17/3.74  ----------------------
% 11.17/3.74  #Subsume      : 95
% 11.17/3.74  #Demod        : 220
% 11.17/3.74  #Tautology    : 126
% 11.17/3.74  #SimpNegUnit  : 0
% 11.17/3.74  #BackRed      : 0
% 11.17/3.74  
% 11.17/3.74  #Partial instantiations: 0
% 11.17/3.74  #Strategies tried      : 1
% 11.17/3.74  
% 11.17/3.74  Timing (in seconds)
% 11.17/3.74  ----------------------
% 11.17/3.74  Preprocessing        : 0.56
% 11.17/3.74  Parsing              : 0.29
% 11.17/3.74  CNF conversion       : 0.04
% 11.17/3.74  Main loop            : 2.36
% 11.17/3.74  Inferencing          : 0.62
% 11.17/3.74  Reduction            : 0.50
% 11.17/3.74  Demodulation         : 0.32
% 11.17/3.74  BG Simplification    : 0.11
% 11.17/3.74  Subsumption          : 0.97
% 11.17/3.74  Abstraction          : 0.10
% 11.17/3.74  MUC search           : 0.00
% 11.17/3.74  Cooper               : 0.00
% 11.17/3.75  Total                : 2.97
% 11.17/3.75  Index Insertion      : 0.00
% 11.17/3.75  Index Deletion       : 0.00
% 11.17/3.75  Index Matching       : 0.00
% 11.17/3.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
