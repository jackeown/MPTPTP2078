%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:30 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 118 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  139 ( 283 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_32,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_36,plain,(
    ! [B_25,A_26] : k3_xboole_0(B_25,A_26) = k3_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_51,plain,(
    ! [B_25,A_26] : r1_tarski(k3_xboole_0(B_25,A_26),A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_6])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_115,plain,(
    ! [B_37,A_38] :
      ( v1_subset_1(B_37,A_38)
      | B_37 = A_38
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_119,plain,(
    ! [A_8,B_9] :
      ( v1_subset_1(A_8,B_9)
      | B_9 = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_115])).

tff(c_145,plain,(
    ! [B_43,A_44] :
      ( ~ v1_subset_1(B_43,A_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_150,plain,(
    ! [A_45,B_46] :
      ( ~ v1_subset_1(A_45,B_46)
      | ~ v1_xboole_0(B_46)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_12,c_145])).

tff(c_155,plain,(
    ! [B_47,A_48] :
      ( ~ v1_xboole_0(B_47)
      | B_47 = A_48
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(resolution,[status(thm)],[c_119,c_150])).

tff(c_164,plain,(
    ! [A_49,B_50] :
      ( ~ v1_xboole_0(A_49)
      | k3_xboole_0(B_50,A_49) = A_49 ) ),
    inference(resolution,[status(thm)],[c_51,c_155])).

tff(c_174,plain,(
    ! [B_53] : k3_xboole_0(B_53,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_164])).

tff(c_191,plain,(
    ! [B_53] : r1_tarski(k1_xboole_0,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_6])).

tff(c_168,plain,(
    ! [B_51,A_52] :
      ( v2_tex_2(B_51,A_52)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ v1_xboole_0(B_51)
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_283,plain,(
    ! [A_63,A_64] :
      ( v2_tex_2(A_63,A_64)
      | ~ v1_xboole_0(A_63)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64)
      | ~ r1_tarski(A_63,u1_struct_0(A_64)) ) ),
    inference(resolution,[status(thm)],[c_12,c_168])).

tff(c_287,plain,(
    ! [A_64] :
      ( v2_tex_2(k1_xboole_0,A_64)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_191,c_283])).

tff(c_298,plain,(
    ! [A_64] :
      ( v2_tex_2(k1_xboole_0,A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_287])).

tff(c_30,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_267,plain,(
    ! [A_58,B_59] :
      ( v3_tex_2('#skF_1'(A_58,B_59),A_58)
      | ~ v2_tex_2(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v3_tdlat_3(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_378,plain,(
    ! [A_74,A_75] :
      ( v3_tex_2('#skF_1'(A_74,A_75),A_74)
      | ~ v2_tex_2(A_75,A_74)
      | ~ l1_pre_topc(A_74)
      | ~ v3_tdlat_3(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74)
      | ~ r1_tarski(A_75,u1_struct_0(A_74)) ) ),
    inference(resolution,[status(thm)],[c_12,c_267])).

tff(c_301,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1('#skF_1'(A_65,B_66),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ v2_tex_2(B_66,A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v3_tdlat_3(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    ! [B_22] :
      ( ~ v3_tex_2(B_22,'#skF_2')
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_321,plain,(
    ! [B_66] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_66),'#skF_2')
      | ~ v2_tex_2(B_66,'#skF_2')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_301,c_26])).

tff(c_330,plain,(
    ! [B_66] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_66),'#skF_2')
      | ~ v2_tex_2(B_66,'#skF_2')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_321])).

tff(c_333,plain,(
    ! [B_68] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_68),'#skF_2')
      | ~ v2_tex_2(B_68,'#skF_2')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_330])).

tff(c_346,plain,(
    ! [A_8] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',A_8),'#skF_2')
      | ~ v2_tex_2(A_8,'#skF_2')
      | ~ r1_tarski(A_8,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_333])).

tff(c_382,plain,(
    ! [A_75] :
      ( ~ v2_tex_2(A_75,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_75,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_378,c_346])).

tff(c_385,plain,(
    ! [A_75] :
      ( ~ v2_tex_2(A_75,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_75,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_382])).

tff(c_387,plain,(
    ! [A_76] :
      ( ~ v2_tex_2(A_76,'#skF_2')
      | ~ r1_tarski(A_76,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_385])).

tff(c_400,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_191,c_387])).

tff(c_405,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_298,c_400])).

tff(c_408,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_405])).

tff(c_410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:21:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.28  
% 2.25/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.28  %$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.25/1.28  
% 2.25/1.28  %Foreground sorts:
% 2.25/1.28  
% 2.25/1.28  
% 2.25/1.28  %Background operators:
% 2.25/1.28  
% 2.25/1.28  
% 2.25/1.28  %Foreground operators:
% 2.25/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.25/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.28  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.25/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.25/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.28  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.25/1.28  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.25/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.28  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.25/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.25/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.25/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.25/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.25/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.25/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.28  
% 2.25/1.30  tff(f_101, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.25/1.30  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.25/1.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.25/1.30  tff(f_30, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.25/1.30  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.25/1.30  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 2.25/1.30  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_subset_1)).
% 2.25/1.30  tff(f_63, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.25/1.30  tff(f_86, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.25/1.30  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.25/1.30  tff(c_32, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.25/1.30  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.25/1.30  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.25/1.30  tff(c_36, plain, (![B_25, A_26]: (k3_xboole_0(B_25, A_26)=k3_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.25/1.30  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.25/1.30  tff(c_51, plain, (![B_25, A_26]: (r1_tarski(k3_xboole_0(B_25, A_26), A_26))), inference(superposition, [status(thm), theory('equality')], [c_36, c_6])).
% 2.25/1.30  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.25/1.30  tff(c_115, plain, (![B_37, A_38]: (v1_subset_1(B_37, A_38) | B_37=A_38 | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.25/1.30  tff(c_119, plain, (![A_8, B_9]: (v1_subset_1(A_8, B_9) | B_9=A_8 | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_12, c_115])).
% 2.25/1.30  tff(c_145, plain, (![B_43, A_44]: (~v1_subset_1(B_43, A_44) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.25/1.30  tff(c_150, plain, (![A_45, B_46]: (~v1_subset_1(A_45, B_46) | ~v1_xboole_0(B_46) | ~r1_tarski(A_45, B_46))), inference(resolution, [status(thm)], [c_12, c_145])).
% 2.25/1.30  tff(c_155, plain, (![B_47, A_48]: (~v1_xboole_0(B_47) | B_47=A_48 | ~r1_tarski(A_48, B_47))), inference(resolution, [status(thm)], [c_119, c_150])).
% 2.25/1.30  tff(c_164, plain, (![A_49, B_50]: (~v1_xboole_0(A_49) | k3_xboole_0(B_50, A_49)=A_49)), inference(resolution, [status(thm)], [c_51, c_155])).
% 2.25/1.30  tff(c_174, plain, (![B_53]: (k3_xboole_0(B_53, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_164])).
% 2.25/1.30  tff(c_191, plain, (![B_53]: (r1_tarski(k1_xboole_0, B_53))), inference(superposition, [status(thm), theory('equality')], [c_174, c_6])).
% 2.25/1.30  tff(c_168, plain, (![B_51, A_52]: (v2_tex_2(B_51, A_52) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_52))) | ~v1_xboole_0(B_51) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.25/1.30  tff(c_283, plain, (![A_63, A_64]: (v2_tex_2(A_63, A_64) | ~v1_xboole_0(A_63) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64) | ~r1_tarski(A_63, u1_struct_0(A_64)))), inference(resolution, [status(thm)], [c_12, c_168])).
% 2.25/1.30  tff(c_287, plain, (![A_64]: (v2_tex_2(k1_xboole_0, A_64) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(resolution, [status(thm)], [c_191, c_283])).
% 2.25/1.30  tff(c_298, plain, (![A_64]: (v2_tex_2(k1_xboole_0, A_64) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_287])).
% 2.25/1.30  tff(c_30, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.25/1.30  tff(c_267, plain, (![A_58, B_59]: (v3_tex_2('#skF_1'(A_58, B_59), A_58) | ~v2_tex_2(B_59, A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v3_tdlat_3(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.25/1.30  tff(c_378, plain, (![A_74, A_75]: (v3_tex_2('#skF_1'(A_74, A_75), A_74) | ~v2_tex_2(A_75, A_74) | ~l1_pre_topc(A_74) | ~v3_tdlat_3(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74) | ~r1_tarski(A_75, u1_struct_0(A_74)))), inference(resolution, [status(thm)], [c_12, c_267])).
% 2.25/1.30  tff(c_301, plain, (![A_65, B_66]: (m1_subset_1('#skF_1'(A_65, B_66), k1_zfmisc_1(u1_struct_0(A_65))) | ~v2_tex_2(B_66, A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v3_tdlat_3(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.25/1.30  tff(c_26, plain, (![B_22]: (~v3_tex_2(B_22, '#skF_2') | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.25/1.30  tff(c_321, plain, (![B_66]: (~v3_tex_2('#skF_1'('#skF_2', B_66), '#skF_2') | ~v2_tex_2(B_66, '#skF_2') | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_301, c_26])).
% 2.25/1.30  tff(c_330, plain, (![B_66]: (~v3_tex_2('#skF_1'('#skF_2', B_66), '#skF_2') | ~v2_tex_2(B_66, '#skF_2') | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_321])).
% 2.25/1.30  tff(c_333, plain, (![B_68]: (~v3_tex_2('#skF_1'('#skF_2', B_68), '#skF_2') | ~v2_tex_2(B_68, '#skF_2') | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_34, c_330])).
% 2.25/1.30  tff(c_346, plain, (![A_8]: (~v3_tex_2('#skF_1'('#skF_2', A_8), '#skF_2') | ~v2_tex_2(A_8, '#skF_2') | ~r1_tarski(A_8, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_333])).
% 2.25/1.30  tff(c_382, plain, (![A_75]: (~v2_tex_2(A_75, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_75, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_378, c_346])).
% 2.25/1.30  tff(c_385, plain, (![A_75]: (~v2_tex_2(A_75, '#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_75, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_382])).
% 2.25/1.30  tff(c_387, plain, (![A_76]: (~v2_tex_2(A_76, '#skF_2') | ~r1_tarski(A_76, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_34, c_385])).
% 2.25/1.30  tff(c_400, plain, (~v2_tex_2(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_191, c_387])).
% 2.25/1.30  tff(c_405, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_298, c_400])).
% 2.25/1.30  tff(c_408, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_405])).
% 2.25/1.30  tff(c_410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_408])).
% 2.25/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.30  
% 2.25/1.30  Inference rules
% 2.25/1.30  ----------------------
% 2.25/1.30  #Ref     : 0
% 2.25/1.30  #Sup     : 78
% 2.25/1.30  #Fact    : 0
% 2.25/1.30  #Define  : 0
% 2.25/1.30  #Split   : 0
% 2.25/1.30  #Chain   : 0
% 2.25/1.30  #Close   : 0
% 2.25/1.30  
% 2.25/1.30  Ordering : KBO
% 2.25/1.30  
% 2.25/1.30  Simplification rules
% 2.25/1.30  ----------------------
% 2.25/1.30  #Subsume      : 9
% 2.25/1.30  #Demod        : 31
% 2.25/1.30  #Tautology    : 31
% 2.25/1.30  #SimpNegUnit  : 4
% 2.25/1.30  #BackRed      : 0
% 2.25/1.30  
% 2.25/1.30  #Partial instantiations: 0
% 2.25/1.30  #Strategies tried      : 1
% 2.25/1.30  
% 2.25/1.30  Timing (in seconds)
% 2.25/1.30  ----------------------
% 2.25/1.30  Preprocessing        : 0.29
% 2.25/1.30  Parsing              : 0.16
% 2.25/1.30  CNF conversion       : 0.02
% 2.25/1.30  Main loop            : 0.24
% 2.25/1.30  Inferencing          : 0.10
% 2.25/1.30  Reduction            : 0.07
% 2.25/1.30  Demodulation         : 0.05
% 2.25/1.30  BG Simplification    : 0.01
% 2.25/1.30  Subsumption          : 0.04
% 2.25/1.30  Abstraction          : 0.01
% 2.25/1.30  MUC search           : 0.00
% 2.25/1.30  Cooper               : 0.00
% 2.25/1.30  Total                : 0.56
% 2.25/1.30  Index Insertion      : 0.00
% 2.25/1.30  Index Deletion       : 0.00
% 2.25/1.30  Index Matching       : 0.00
% 2.25/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
