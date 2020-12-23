%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:39 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 182 expanded)
%              Number of leaves         :   28 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  104 ( 418 expanded)
%              Number of equality atoms :   31 ( 103 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_47,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_18,c_42])).

tff(c_51,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_47])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_34])).

tff(c_117,plain,(
    ! [A_39,B_40,C_41] :
      ( k9_subset_1(A_39,B_40,C_41) = k3_xboole_0(B_40,C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_125,plain,(
    ! [B_40] : k9_subset_1(k2_struct_0('#skF_1'),B_40,'#skF_2') = k3_xboole_0(B_40,'#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_117])).

tff(c_26,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_52,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_26])).

tff(c_128,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_52])).

tff(c_28,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_53,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_30])).

tff(c_64,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_72,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_53,c_64])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_72,c_8])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_147,plain,(
    ! [B_44,B_45,A_46] :
      ( k9_subset_1(B_44,B_45,A_46) = k3_xboole_0(B_45,A_46)
      | ~ r1_tarski(A_46,B_44) ) ),
    inference(resolution,[status(thm)],[c_14,c_117])).

tff(c_158,plain,(
    ! [B_2,B_45] : k9_subset_1(B_2,B_45,B_2) = k3_xboole_0(B_45,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_147])).

tff(c_32,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_179,plain,(
    ! [A_51,B_52] :
      ( k2_pre_topc(A_51,B_52) = k2_struct_0(A_51)
      | ~ v1_tops_1(B_52,A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_186,plain,(
    ! [B_52] :
      ( k2_pre_topc('#skF_1',B_52) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_52,'#skF_1')
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_179])).

tff(c_206,plain,(
    ! [B_54] :
      ( k2_pre_topc('#skF_1',B_54) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_54,'#skF_1')
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_186])).

tff(c_213,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_206])).

tff(c_220,plain,(
    k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_213])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_246,plain,(
    ! [A_56,B_57,C_58] :
      ( k2_pre_topc(A_56,k9_subset_1(u1_struct_0(A_56),B_57,k2_pre_topc(A_56,C_58))) = k2_pre_topc(A_56,k9_subset_1(u1_struct_0(A_56),B_57,C_58))
      | ~ v3_pre_topc(B_57,A_56)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_264,plain,(
    ! [B_57,C_58] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),B_57,k2_pre_topc('#skF_1',C_58))) = k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_57,C_58))
      | ~ v3_pre_topc(B_57,'#skF_1')
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_246])).

tff(c_301,plain,(
    ! [B_62,C_63] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),B_62,k2_pre_topc('#skF_1',C_63))) = k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),B_62,C_63))
      | ~ v3_pre_topc(B_62,'#skF_1')
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_51,c_51,c_51,c_264])).

tff(c_323,plain,(
    ! [B_62] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),B_62,k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),B_62,'#skF_2'))
      | ~ v3_pre_topc(B_62,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_301])).

tff(c_361,plain,(
    ! [B_68] :
      ( k2_pre_topc('#skF_1',k3_xboole_0(B_68,k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k3_xboole_0(B_68,'#skF_2'))
      | ~ v3_pre_topc(B_68,'#skF_1')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_158,c_125,c_323])).

tff(c_371,plain,
    ( k2_pre_topc('#skF_1',k3_xboole_0('#skF_3',k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2'))
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_53,c_361])).

tff(c_377,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_89,c_371])).

tff(c_379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_377])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.35  
% 2.67/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.35  %$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.67/1.35  
% 2.67/1.35  %Foreground sorts:
% 2.67/1.35  
% 2.67/1.35  
% 2.67/1.35  %Background operators:
% 2.67/1.35  
% 2.67/1.35  
% 2.67/1.35  %Foreground operators:
% 2.67/1.35  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.67/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.67/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.35  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.67/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.67/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.67/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.67/1.35  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.67/1.35  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.67/1.35  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.67/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.35  
% 2.67/1.37  tff(f_91, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tops_1)).
% 2.67/1.37  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.67/1.37  tff(f_47, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.67/1.37  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.67/1.37  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.67/1.37  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.67/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.67/1.37  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 2.67/1.37  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tops_1)).
% 2.67/1.37  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.67/1.37  tff(c_18, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.67/1.37  tff(c_42, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.67/1.37  tff(c_47, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_18, c_42])).
% 2.67/1.37  tff(c_51, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_47])).
% 2.67/1.37  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.67/1.37  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_34])).
% 2.67/1.37  tff(c_117, plain, (![A_39, B_40, C_41]: (k9_subset_1(A_39, B_40, C_41)=k3_xboole_0(B_40, C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.67/1.37  tff(c_125, plain, (![B_40]: (k9_subset_1(k2_struct_0('#skF_1'), B_40, '#skF_2')=k3_xboole_0(B_40, '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_117])).
% 2.67/1.37  tff(c_26, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.67/1.37  tff(c_52, plain, (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_26])).
% 2.67/1.37  tff(c_128, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_52])).
% 2.67/1.37  tff(c_28, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.67/1.37  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.67/1.37  tff(c_53, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_30])).
% 2.67/1.37  tff(c_64, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.67/1.37  tff(c_72, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_53, c_64])).
% 2.67/1.37  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.67/1.37  tff(c_89, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(resolution, [status(thm)], [c_72, c_8])).
% 2.67/1.37  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.37  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.67/1.37  tff(c_147, plain, (![B_44, B_45, A_46]: (k9_subset_1(B_44, B_45, A_46)=k3_xboole_0(B_45, A_46) | ~r1_tarski(A_46, B_44))), inference(resolution, [status(thm)], [c_14, c_117])).
% 2.67/1.37  tff(c_158, plain, (![B_2, B_45]: (k9_subset_1(B_2, B_45, B_2)=k3_xboole_0(B_45, B_2))), inference(resolution, [status(thm)], [c_6, c_147])).
% 2.67/1.37  tff(c_32, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.67/1.37  tff(c_179, plain, (![A_51, B_52]: (k2_pre_topc(A_51, B_52)=k2_struct_0(A_51) | ~v1_tops_1(B_52, A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.67/1.37  tff(c_186, plain, (![B_52]: (k2_pre_topc('#skF_1', B_52)=k2_struct_0('#skF_1') | ~v1_tops_1(B_52, '#skF_1') | ~m1_subset_1(B_52, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_179])).
% 2.67/1.37  tff(c_206, plain, (![B_54]: (k2_pre_topc('#skF_1', B_54)=k2_struct_0('#skF_1') | ~v1_tops_1(B_54, '#skF_1') | ~m1_subset_1(B_54, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_186])).
% 2.67/1.37  tff(c_213, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_206])).
% 2.67/1.37  tff(c_220, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_213])).
% 2.67/1.37  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.67/1.37  tff(c_246, plain, (![A_56, B_57, C_58]: (k2_pre_topc(A_56, k9_subset_1(u1_struct_0(A_56), B_57, k2_pre_topc(A_56, C_58)))=k2_pre_topc(A_56, k9_subset_1(u1_struct_0(A_56), B_57, C_58)) | ~v3_pre_topc(B_57, A_56) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.67/1.37  tff(c_264, plain, (![B_57, C_58]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), B_57, k2_pre_topc('#skF_1', C_58)))=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_57, C_58)) | ~v3_pre_topc(B_57, '#skF_1') | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_246])).
% 2.67/1.37  tff(c_301, plain, (![B_62, C_63]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), B_62, k2_pre_topc('#skF_1', C_63)))=k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), B_62, C_63)) | ~v3_pre_topc(B_62, '#skF_1') | ~m1_subset_1(C_63, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_51, c_51, c_51, c_264])).
% 2.67/1.37  tff(c_323, plain, (![B_62]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), B_62, k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), B_62, '#skF_2')) | ~v3_pre_topc(B_62, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_220, c_301])).
% 2.67/1.37  tff(c_361, plain, (![B_68]: (k2_pre_topc('#skF_1', k3_xboole_0(B_68, k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k3_xboole_0(B_68, '#skF_2')) | ~v3_pre_topc(B_68, '#skF_1') | ~m1_subset_1(B_68, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_158, c_125, c_323])).
% 2.67/1.37  tff(c_371, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')) | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_53, c_361])).
% 2.67/1.37  tff(c_377, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_89, c_371])).
% 2.67/1.37  tff(c_379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_377])).
% 2.67/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.37  
% 2.67/1.37  Inference rules
% 2.67/1.37  ----------------------
% 2.67/1.37  #Ref     : 0
% 2.67/1.37  #Sup     : 72
% 2.67/1.37  #Fact    : 0
% 2.67/1.37  #Define  : 0
% 2.67/1.37  #Split   : 4
% 2.67/1.37  #Chain   : 0
% 2.67/1.37  #Close   : 0
% 2.67/1.37  
% 2.67/1.37  Ordering : KBO
% 2.67/1.37  
% 2.67/1.37  Simplification rules
% 2.67/1.37  ----------------------
% 2.67/1.37  #Subsume      : 6
% 2.67/1.37  #Demod        : 56
% 2.67/1.37  #Tautology    : 30
% 2.67/1.37  #SimpNegUnit  : 7
% 2.67/1.37  #BackRed      : 4
% 2.67/1.37  
% 2.67/1.37  #Partial instantiations: 0
% 2.67/1.37  #Strategies tried      : 1
% 2.67/1.37  
% 2.67/1.37  Timing (in seconds)
% 2.67/1.37  ----------------------
% 2.67/1.37  Preprocessing        : 0.32
% 2.67/1.37  Parsing              : 0.17
% 2.67/1.37  CNF conversion       : 0.02
% 2.67/1.37  Main loop            : 0.28
% 2.67/1.37  Inferencing          : 0.10
% 2.67/1.37  Reduction            : 0.09
% 2.67/1.37  Demodulation         : 0.07
% 2.67/1.37  BG Simplification    : 0.02
% 2.67/1.37  Subsumption          : 0.05
% 2.67/1.37  Abstraction          : 0.02
% 2.67/1.37  MUC search           : 0.00
% 2.67/1.37  Cooper               : 0.00
% 2.67/1.37  Total                : 0.63
% 2.67/1.37  Index Insertion      : 0.00
% 2.67/1.37  Index Deletion       : 0.00
% 2.67/1.37  Index Matching       : 0.00
% 2.67/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
