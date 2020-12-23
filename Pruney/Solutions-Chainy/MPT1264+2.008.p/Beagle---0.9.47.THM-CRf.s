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
% DateTime   : Thu Dec  3 10:21:39 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 226 expanded)
%              Number of leaves         :   30 (  92 expanded)
%              Depth                    :   12
%              Number of atoms          :  120 ( 519 expanded)
%              Number of equality atoms :   39 ( 132 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v1_tops_1(B,A)
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( v3_pre_topc(C,A)
                   => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C))) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_24,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_53,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_24,c_48])).

tff(c_57,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_53])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_40])).

tff(c_94,plain,(
    ! [A_41,B_42,C_43] :
      ( k9_subset_1(A_41,B_42,C_43) = k3_xboole_0(B_42,C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_102,plain,(
    ! [B_42] : k9_subset_1(k2_struct_0('#skF_2'),B_42,'#skF_3') = k3_xboole_0(B_42,'#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_94])).

tff(c_32,plain,(
    k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_58,plain,(
    k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),'#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_32])).

tff(c_114,plain,(
    k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_58])).

tff(c_34,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_59,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_36])).

tff(c_66,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_78,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_59,c_66])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_431,plain,(
    ! [A_78,B_79,C_80] :
      ( r1_tarski('#skF_1'(A_78,B_79,C_80),C_80)
      | k3_xboole_0(B_79,C_80) = A_78
      | ~ r1_tarski(A_78,C_80)
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r1_tarski('#skF_1'(A_3,B_4,C_5),A_3)
      | k3_xboole_0(B_4,C_5) = A_3
      | ~ r1_tarski(A_3,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_439,plain,(
    ! [B_79,C_80] :
      ( k3_xboole_0(B_79,C_80) = C_80
      | ~ r1_tarski(C_80,C_80)
      | ~ r1_tarski(C_80,B_79) ) ),
    inference(resolution,[status(thm)],[c_431,c_8])).

tff(c_468,plain,(
    ! [B_81,C_82] :
      ( k3_xboole_0(B_81,C_82) = C_82
      | ~ r1_tarski(C_82,B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_439])).

tff(c_482,plain,(
    k3_xboole_0(k2_struct_0('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_78,c_468])).

tff(c_103,plain,(
    ! [B_42] : k9_subset_1(k2_struct_0('#skF_2'),B_42,'#skF_4') = k3_xboole_0(B_42,'#skF_4') ),
    inference(resolution,[status(thm)],[c_59,c_94])).

tff(c_104,plain,(
    ! [A_44,C_45,B_46] :
      ( k9_subset_1(A_44,C_45,B_46) = k9_subset_1(A_44,B_46,C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_113,plain,(
    ! [B_46] : k9_subset_1(k2_struct_0('#skF_2'),B_46,'#skF_4') = k9_subset_1(k2_struct_0('#skF_2'),'#skF_4',B_46) ),
    inference(resolution,[status(thm)],[c_59,c_104])).

tff(c_212,plain,(
    ! [B_57] : k9_subset_1(k2_struct_0('#skF_2'),'#skF_4',B_57) = k3_xboole_0(B_57,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_113])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_166,plain,(
    ! [B_50,B_51,A_52] :
      ( k9_subset_1(B_50,B_51,A_52) = k3_xboole_0(B_51,A_52)
      | ~ r1_tarski(A_52,B_50) ) ),
    inference(resolution,[status(thm)],[c_20,c_94])).

tff(c_177,plain,(
    ! [B_2,B_51] : k9_subset_1(B_2,B_51,B_2) = k3_xboole_0(B_51,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_166])).

tff(c_219,plain,(
    k3_xboole_0(k2_struct_0('#skF_2'),'#skF_4') = k3_xboole_0('#skF_4',k2_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_177])).

tff(c_494,plain,(
    k3_xboole_0('#skF_4',k2_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_219])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_38,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_322,plain,(
    ! [A_64,B_65] :
      ( k2_pre_topc(A_64,B_65) = k2_struct_0(A_64)
      | ~ v1_tops_1(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_329,plain,(
    ! [B_65] :
      ( k2_pre_topc('#skF_2',B_65) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_65,'#skF_2')
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_322])).

tff(c_349,plain,(
    ! [B_67] :
      ( k2_pre_topc('#skF_2',B_67) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_67,'#skF_2')
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_329])).

tff(c_356,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_349])).

tff(c_363,plain,(
    k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_356])).

tff(c_640,plain,(
    ! [A_109,B_110,C_111] :
      ( k2_pre_topc(A_109,k9_subset_1(u1_struct_0(A_109),B_110,k2_pre_topc(A_109,C_111))) = k2_pre_topc(A_109,k9_subset_1(u1_struct_0(A_109),B_110,C_111))
      | ~ v3_pre_topc(B_110,A_109)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_655,plain,(
    ! [B_110] :
      ( k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),B_110,k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),B_110,'#skF_3'))
      | ~ v3_pre_topc(B_110,'#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_640])).

tff(c_670,plain,(
    ! [B_112] :
      ( k2_pre_topc('#skF_2',k3_xboole_0(B_112,k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k3_xboole_0(B_112,'#skF_3'))
      | ~ v3_pre_topc(B_112,'#skF_2')
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_57,c_60,c_57,c_177,c_102,c_57,c_57,c_655])).

tff(c_680,plain,
    ( k2_pre_topc('#skF_2',k3_xboole_0('#skF_4',k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3'))
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_59,c_670])).

tff(c_686,plain,(
    k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3')) = k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_494,c_680])).

tff(c_688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_686])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.91  
% 3.42/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.92  %$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.42/1.92  
% 3.42/1.92  %Foreground sorts:
% 3.42/1.92  
% 3.42/1.92  
% 3.42/1.92  %Background operators:
% 3.42/1.92  
% 3.42/1.92  
% 3.42/1.92  %Foreground operators:
% 3.42/1.92  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.42/1.92  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.42/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.92  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.42/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.42/1.92  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.42/1.92  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.92  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.42/1.92  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.42/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.92  tff('#skF_4', type, '#skF_4': $i).
% 3.42/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.92  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.42/1.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.42/1.92  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.42/1.92  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.42/1.92  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.42/1.92  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.42/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.42/1.92  
% 3.73/1.94  tff(f_104, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 3.73/1.94  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.73/1.94  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.73/1.94  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.73/1.94  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.73/1.94  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.73/1.94  tff(f_44, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 3.73/1.94  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.73/1.94  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 3.73/1.94  tff(f_87, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_1)).
% 3.73/1.94  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.73/1.94  tff(c_24, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.73/1.94  tff(c_48, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.73/1.94  tff(c_53, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_24, c_48])).
% 3.73/1.94  tff(c_57, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_53])).
% 3.73/1.94  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.73/1.94  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_40])).
% 3.73/1.94  tff(c_94, plain, (![A_41, B_42, C_43]: (k9_subset_1(A_41, B_42, C_43)=k3_xboole_0(B_42, C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.73/1.94  tff(c_102, plain, (![B_42]: (k9_subset_1(k2_struct_0('#skF_2'), B_42, '#skF_3')=k3_xboole_0(B_42, '#skF_3'))), inference(resolution, [status(thm)], [c_60, c_94])).
% 3.73/1.94  tff(c_32, plain, (k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.73/1.94  tff(c_58, plain, (k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), '#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_32])).
% 3.73/1.94  tff(c_114, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_58])).
% 3.73/1.94  tff(c_34, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.73/1.94  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.73/1.94  tff(c_59, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_36])).
% 3.73/1.94  tff(c_66, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.73/1.94  tff(c_78, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_59, c_66])).
% 3.73/1.94  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.73/1.94  tff(c_431, plain, (![A_78, B_79, C_80]: (r1_tarski('#skF_1'(A_78, B_79, C_80), C_80) | k3_xboole_0(B_79, C_80)=A_78 | ~r1_tarski(A_78, C_80) | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.73/1.94  tff(c_8, plain, (![A_3, B_4, C_5]: (~r1_tarski('#skF_1'(A_3, B_4, C_5), A_3) | k3_xboole_0(B_4, C_5)=A_3 | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.73/1.94  tff(c_439, plain, (![B_79, C_80]: (k3_xboole_0(B_79, C_80)=C_80 | ~r1_tarski(C_80, C_80) | ~r1_tarski(C_80, B_79))), inference(resolution, [status(thm)], [c_431, c_8])).
% 3.73/1.94  tff(c_468, plain, (![B_81, C_82]: (k3_xboole_0(B_81, C_82)=C_82 | ~r1_tarski(C_82, B_81))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_439])).
% 3.73/1.94  tff(c_482, plain, (k3_xboole_0(k2_struct_0('#skF_2'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_78, c_468])).
% 3.73/1.94  tff(c_103, plain, (![B_42]: (k9_subset_1(k2_struct_0('#skF_2'), B_42, '#skF_4')=k3_xboole_0(B_42, '#skF_4'))), inference(resolution, [status(thm)], [c_59, c_94])).
% 3.73/1.94  tff(c_104, plain, (![A_44, C_45, B_46]: (k9_subset_1(A_44, C_45, B_46)=k9_subset_1(A_44, B_46, C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.73/1.94  tff(c_113, plain, (![B_46]: (k9_subset_1(k2_struct_0('#skF_2'), B_46, '#skF_4')=k9_subset_1(k2_struct_0('#skF_2'), '#skF_4', B_46))), inference(resolution, [status(thm)], [c_59, c_104])).
% 3.73/1.94  tff(c_212, plain, (![B_57]: (k9_subset_1(k2_struct_0('#skF_2'), '#skF_4', B_57)=k3_xboole_0(B_57, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_113])).
% 3.73/1.94  tff(c_20, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.73/1.94  tff(c_166, plain, (![B_50, B_51, A_52]: (k9_subset_1(B_50, B_51, A_52)=k3_xboole_0(B_51, A_52) | ~r1_tarski(A_52, B_50))), inference(resolution, [status(thm)], [c_20, c_94])).
% 3.73/1.94  tff(c_177, plain, (![B_2, B_51]: (k9_subset_1(B_2, B_51, B_2)=k3_xboole_0(B_51, B_2))), inference(resolution, [status(thm)], [c_6, c_166])).
% 3.73/1.94  tff(c_219, plain, (k3_xboole_0(k2_struct_0('#skF_2'), '#skF_4')=k3_xboole_0('#skF_4', k2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_212, c_177])).
% 3.73/1.94  tff(c_494, plain, (k3_xboole_0('#skF_4', k2_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_482, c_219])).
% 3.73/1.94  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.73/1.94  tff(c_38, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.73/1.94  tff(c_322, plain, (![A_64, B_65]: (k2_pre_topc(A_64, B_65)=k2_struct_0(A_64) | ~v1_tops_1(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.73/1.94  tff(c_329, plain, (![B_65]: (k2_pre_topc('#skF_2', B_65)=k2_struct_0('#skF_2') | ~v1_tops_1(B_65, '#skF_2') | ~m1_subset_1(B_65, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_57, c_322])).
% 3.73/1.94  tff(c_349, plain, (![B_67]: (k2_pre_topc('#skF_2', B_67)=k2_struct_0('#skF_2') | ~v1_tops_1(B_67, '#skF_2') | ~m1_subset_1(B_67, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_329])).
% 3.73/1.94  tff(c_356, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_349])).
% 3.73/1.94  tff(c_363, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_356])).
% 3.73/1.94  tff(c_640, plain, (![A_109, B_110, C_111]: (k2_pre_topc(A_109, k9_subset_1(u1_struct_0(A_109), B_110, k2_pre_topc(A_109, C_111)))=k2_pre_topc(A_109, k9_subset_1(u1_struct_0(A_109), B_110, C_111)) | ~v3_pre_topc(B_110, A_109) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(A_109))) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.73/1.94  tff(c_655, plain, (![B_110]: (k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), B_110, k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), B_110, '#skF_3')) | ~v3_pre_topc(B_110, '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_363, c_640])).
% 3.73/1.94  tff(c_670, plain, (![B_112]: (k2_pre_topc('#skF_2', k3_xboole_0(B_112, k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k3_xboole_0(B_112, '#skF_3')) | ~v3_pre_topc(B_112, '#skF_2') | ~m1_subset_1(B_112, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_57, c_60, c_57, c_177, c_102, c_57, c_57, c_655])).
% 3.73/1.94  tff(c_680, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3')) | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_59, c_670])).
% 3.73/1.94  tff(c_686, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_494, c_680])).
% 3.73/1.94  tff(c_688, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_686])).
% 3.73/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.94  
% 3.73/1.94  Inference rules
% 3.73/1.94  ----------------------
% 3.73/1.94  #Ref     : 0
% 3.73/1.94  #Sup     : 141
% 3.73/1.94  #Fact    : 0
% 3.73/1.94  #Define  : 0
% 3.73/1.94  #Split   : 4
% 3.73/1.94  #Chain   : 0
% 3.73/1.94  #Close   : 0
% 3.73/1.94  
% 3.73/1.94  Ordering : KBO
% 3.73/1.94  
% 3.73/1.94  Simplification rules
% 3.73/1.94  ----------------------
% 3.73/1.94  #Subsume      : 6
% 3.73/1.94  #Demod        : 73
% 3.73/1.94  #Tautology    : 76
% 3.73/1.94  #SimpNegUnit  : 6
% 3.73/1.94  #BackRed      : 6
% 3.73/1.94  
% 3.73/1.94  #Partial instantiations: 0
% 3.73/1.94  #Strategies tried      : 1
% 3.73/1.94  
% 3.73/1.94  Timing (in seconds)
% 3.73/1.94  ----------------------
% 3.73/1.95  Preprocessing        : 0.50
% 3.73/1.95  Parsing              : 0.26
% 3.73/1.95  CNF conversion       : 0.04
% 3.73/1.95  Main loop            : 0.58
% 3.73/1.95  Inferencing          : 0.22
% 3.73/1.95  Reduction            : 0.18
% 3.73/1.95  Demodulation         : 0.13
% 3.73/1.95  BG Simplification    : 0.03
% 3.73/1.95  Subsumption          : 0.12
% 3.73/1.95  Abstraction          : 0.04
% 3.73/1.95  MUC search           : 0.00
% 3.73/1.95  Cooper               : 0.00
% 3.73/1.95  Total                : 1.14
% 3.73/1.95  Index Insertion      : 0.00
% 3.73/1.95  Index Deletion       : 0.00
% 3.73/1.95  Index Matching       : 0.00
% 3.73/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
