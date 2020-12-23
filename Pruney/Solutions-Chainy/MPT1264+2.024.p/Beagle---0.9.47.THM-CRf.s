%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:41 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 225 expanded)
%              Number of leaves         :   30 (  92 expanded)
%              Depth                    :   12
%              Number of atoms          :  105 ( 504 expanded)
%              Number of equality atoms :   27 ( 115 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_91,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_74,axiom,(
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

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_43,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_16,c_38])).

tff(c_47,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_43])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_49,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_32])).

tff(c_168,plain,(
    ! [A_44,B_45,C_46] :
      ( k9_subset_1(A_44,B_45,C_46) = k3_xboole_0(B_45,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_183,plain,(
    ! [B_45] : k9_subset_1(k2_struct_0('#skF_1'),B_45,'#skF_2') = k3_xboole_0(B_45,'#skF_2') ),
    inference(resolution,[status(thm)],[c_49,c_168])).

tff(c_24,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_48,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_24])).

tff(c_193,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_48])).

tff(c_26,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_28])).

tff(c_57,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_95,plain,(
    ! [A_38] :
      ( m1_subset_1(k2_struct_0(A_38),k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_103,plain,(
    ! [A_39] :
      ( r1_tarski(k2_struct_0(A_39),u1_struct_0(A_39))
      | ~ l1_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_95,c_8])).

tff(c_109,plain,
    ( r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_103])).

tff(c_111,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_127,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_111])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_127])).

tff(c_133,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_101,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_95])).

tff(c_144,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_101])).

tff(c_179,plain,(
    ! [B_45] : k9_subset_1(k2_struct_0('#skF_1'),B_45,k2_struct_0('#skF_1')) = k3_xboole_0(B_45,k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_144,c_168])).

tff(c_30,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_203,plain,(
    ! [A_49,B_50] :
      ( k2_pre_topc(A_49,B_50) = k2_struct_0(A_49)
      | ~ v1_tops_1(B_50,A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_213,plain,(
    ! [B_50] :
      ( k2_pre_topc('#skF_1',B_50) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_50,'#skF_1')
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_203])).

tff(c_242,plain,(
    ! [B_55] :
      ( k2_pre_topc('#skF_1',B_55) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_55,'#skF_1')
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_213])).

tff(c_255,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_49,c_242])).

tff(c_261,plain,(
    k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_255])).

tff(c_363,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_pre_topc(A_64,k9_subset_1(u1_struct_0(A_64),B_65,k2_pre_topc(A_64,C_66))) = k2_pre_topc(A_64,k9_subset_1(u1_struct_0(A_64),B_65,C_66))
      | ~ v3_pre_topc(B_65,A_64)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_378,plain,(
    ! [B_65] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_65,k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_65,'#skF_2'))
      | ~ v3_pre_topc(B_65,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_363])).

tff(c_444,plain,(
    ! [B_74] :
      ( k2_pre_topc('#skF_1',k3_xboole_0(B_74,k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k3_xboole_0(B_74,'#skF_2'))
      | ~ v3_pre_topc(B_74,'#skF_1')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_47,c_49,c_47,c_179,c_183,c_47,c_47,c_378])).

tff(c_454,plain,
    ( k2_pre_topc('#skF_1',k3_xboole_0('#skF_3',k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2'))
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_444])).

tff(c_463,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_73,c_454])).

tff(c_465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_463])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:58:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.36  
% 2.61/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.36  %$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.70/1.36  
% 2.70/1.36  %Foreground sorts:
% 2.70/1.36  
% 2.70/1.36  
% 2.70/1.36  %Background operators:
% 2.70/1.36  
% 2.70/1.36  
% 2.70/1.36  %Foreground operators:
% 2.70/1.36  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.70/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.70/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.36  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.70/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.70/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.70/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.70/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.70/1.36  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.70/1.36  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.70/1.36  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.70/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.70/1.36  
% 2.70/1.38  tff(f_91, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 2.70/1.38  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.70/1.38  tff(f_43, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.70/1.38  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.70/1.38  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.70/1.38  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.70/1.38  tff(f_47, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.70/1.38  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 2.70/1.38  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_1)).
% 2.70/1.38  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.70/1.38  tff(c_16, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.70/1.38  tff(c_38, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.38  tff(c_43, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_16, c_38])).
% 2.70/1.38  tff(c_47, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_43])).
% 2.70/1.38  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.70/1.38  tff(c_49, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_32])).
% 2.70/1.38  tff(c_168, plain, (![A_44, B_45, C_46]: (k9_subset_1(A_44, B_45, C_46)=k3_xboole_0(B_45, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.38  tff(c_183, plain, (![B_45]: (k9_subset_1(k2_struct_0('#skF_1'), B_45, '#skF_2')=k3_xboole_0(B_45, '#skF_2'))), inference(resolution, [status(thm)], [c_49, c_168])).
% 2.70/1.38  tff(c_24, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.70/1.38  tff(c_48, plain, (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_24])).
% 2.70/1.38  tff(c_193, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_48])).
% 2.70/1.38  tff(c_26, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.70/1.38  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.70/1.38  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_28])).
% 2.70/1.38  tff(c_57, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.70/1.38  tff(c_68, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_57])).
% 2.70/1.38  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.70/1.38  tff(c_73, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(resolution, [status(thm)], [c_68, c_2])).
% 2.70/1.38  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.70/1.38  tff(c_95, plain, (![A_38]: (m1_subset_1(k2_struct_0(A_38), k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.70/1.38  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.70/1.38  tff(c_103, plain, (![A_39]: (r1_tarski(k2_struct_0(A_39), u1_struct_0(A_39)) | ~l1_struct_0(A_39))), inference(resolution, [status(thm)], [c_95, c_8])).
% 2.70/1.38  tff(c_109, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_47, c_103])).
% 2.70/1.38  tff(c_111, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_109])).
% 2.70/1.38  tff(c_127, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_111])).
% 2.70/1.38  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_127])).
% 2.70/1.38  tff(c_133, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_109])).
% 2.70/1.38  tff(c_101, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_47, c_95])).
% 2.70/1.38  tff(c_144, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_101])).
% 2.70/1.38  tff(c_179, plain, (![B_45]: (k9_subset_1(k2_struct_0('#skF_1'), B_45, k2_struct_0('#skF_1'))=k3_xboole_0(B_45, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_144, c_168])).
% 2.70/1.38  tff(c_30, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.70/1.38  tff(c_203, plain, (![A_49, B_50]: (k2_pre_topc(A_49, B_50)=k2_struct_0(A_49) | ~v1_tops_1(B_50, A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.70/1.38  tff(c_213, plain, (![B_50]: (k2_pre_topc('#skF_1', B_50)=k2_struct_0('#skF_1') | ~v1_tops_1(B_50, '#skF_1') | ~m1_subset_1(B_50, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_47, c_203])).
% 2.70/1.38  tff(c_242, plain, (![B_55]: (k2_pre_topc('#skF_1', B_55)=k2_struct_0('#skF_1') | ~v1_tops_1(B_55, '#skF_1') | ~m1_subset_1(B_55, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_213])).
% 2.70/1.38  tff(c_255, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_49, c_242])).
% 2.70/1.38  tff(c_261, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_255])).
% 2.70/1.38  tff(c_363, plain, (![A_64, B_65, C_66]: (k2_pre_topc(A_64, k9_subset_1(u1_struct_0(A_64), B_65, k2_pre_topc(A_64, C_66)))=k2_pre_topc(A_64, k9_subset_1(u1_struct_0(A_64), B_65, C_66)) | ~v3_pre_topc(B_65, A_64) | ~m1_subset_1(C_66, k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.70/1.38  tff(c_378, plain, (![B_65]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_65, k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_65, '#skF_2')) | ~v3_pre_topc(B_65, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_261, c_363])).
% 2.70/1.38  tff(c_444, plain, (![B_74]: (k2_pre_topc('#skF_1', k3_xboole_0(B_74, k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k3_xboole_0(B_74, '#skF_2')) | ~v3_pre_topc(B_74, '#skF_1') | ~m1_subset_1(B_74, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_47, c_49, c_47, c_179, c_183, c_47, c_47, c_378])).
% 2.70/1.38  tff(c_454, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')) | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_444])).
% 2.70/1.38  tff(c_463, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_73, c_454])).
% 2.70/1.38  tff(c_465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_193, c_463])).
% 2.70/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.38  
% 2.70/1.38  Inference rules
% 2.70/1.38  ----------------------
% 2.70/1.38  #Ref     : 0
% 2.70/1.38  #Sup     : 95
% 2.70/1.38  #Fact    : 0
% 2.70/1.38  #Define  : 0
% 2.70/1.38  #Split   : 3
% 2.70/1.38  #Chain   : 0
% 2.70/1.38  #Close   : 0
% 2.70/1.38  
% 2.70/1.38  Ordering : KBO
% 2.70/1.38  
% 2.70/1.38  Simplification rules
% 2.70/1.38  ----------------------
% 2.70/1.38  #Subsume      : 10
% 2.70/1.38  #Demod        : 61
% 2.70/1.38  #Tautology    : 38
% 2.70/1.38  #SimpNegUnit  : 7
% 2.70/1.38  #BackRed      : 4
% 2.70/1.38  
% 2.70/1.38  #Partial instantiations: 0
% 2.70/1.38  #Strategies tried      : 1
% 2.70/1.38  
% 2.70/1.38  Timing (in seconds)
% 2.70/1.38  ----------------------
% 2.70/1.38  Preprocessing        : 0.31
% 2.70/1.38  Parsing              : 0.16
% 2.70/1.38  CNF conversion       : 0.02
% 2.70/1.38  Main loop            : 0.27
% 2.70/1.38  Inferencing          : 0.11
% 2.70/1.38  Reduction            : 0.09
% 2.70/1.38  Demodulation         : 0.06
% 2.70/1.38  BG Simplification    : 0.02
% 2.70/1.38  Subsumption          : 0.04
% 2.70/1.38  Abstraction          : 0.02
% 2.70/1.38  MUC search           : 0.00
% 2.70/1.38  Cooper               : 0.00
% 2.70/1.38  Total                : 0.62
% 2.70/1.38  Index Insertion      : 0.00
% 2.70/1.38  Index Deletion       : 0.00
% 2.70/1.38  Index Matching       : 0.00
% 2.70/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
