%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:41 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 206 expanded)
%              Number of leaves         :   29 (  84 expanded)
%              Depth                    :   11
%              Number of atoms          :  122 ( 508 expanded)
%              Number of equality atoms :   35 (  89 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v1_tops_1(B,A)
                    & v1_tops_1(C,A)
                    & v3_pre_topc(C,A) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_70,axiom,(
    ! [A] :
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

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_69,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_74,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(resolution,[status(thm)],[c_12,c_69])).

tff(c_78,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_74])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_81,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_30])).

tff(c_159,plain,(
    ! [A_41,B_42,C_43] :
      ( k9_subset_1(A_41,B_42,C_43) = k3_xboole_0(B_42,C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_169,plain,(
    ! [B_44] : k9_subset_1(k2_struct_0('#skF_1'),B_44,'#skF_2') = k3_xboole_0(B_44,'#skF_2') ),
    inference(resolution,[status(thm)],[c_81,c_159])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k9_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    ! [B_44] :
      ( m1_subset_1(k3_xboole_0(B_44,'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_4])).

tff(c_181,plain,(
    ! [B_44] : m1_subset_1(k3_xboole_0(B_44,'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_175])).

tff(c_306,plain,(
    ! [B_56,A_57] :
      ( v1_tops_1(B_56,A_57)
      | k2_pre_topc(A_57,B_56) != k2_struct_0(A_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_313,plain,(
    ! [B_56] :
      ( v1_tops_1(B_56,'#skF_1')
      | k2_pre_topc('#skF_1',B_56) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_306])).

tff(c_362,plain,(
    ! [B_62] :
      ( v1_tops_1(B_62,'#skF_1')
      | k2_pre_topc('#skF_1',B_62) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_313])).

tff(c_783,plain,(
    ! [B_88] :
      ( v1_tops_1(k3_xboole_0(B_88,'#skF_2'),'#skF_1')
      | k2_pre_topc('#skF_1',k3_xboole_0(B_88,'#skF_2')) != k2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_181,c_362])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_86,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [B_34,A_35] : k1_setfam_1(k2_tarski(B_34,A_35)) = k3_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_86])).

tff(c_8,plain,(
    ! [A_9,B_10] : k1_setfam_1(k2_tarski(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_107,plain,(
    ! [B_34,A_35] : k3_xboole_0(B_34,A_35) = k3_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_8])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_28])).

tff(c_168,plain,(
    ! [B_42] : k9_subset_1(k2_struct_0('#skF_1'),B_42,'#skF_3') = k3_xboole_0(B_42,'#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_159])).

tff(c_20,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_79,plain,(
    ~ v1_tops_1(k9_subset_1(k2_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_20])).

tff(c_221,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_79])).

tff(c_222,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_221])).

tff(c_799,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_783,c_222])).

tff(c_26,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_167,plain,(
    ! [B_42] : k9_subset_1(k2_struct_0('#skF_1'),B_42,'#skF_2') = k3_xboole_0(B_42,'#skF_2') ),
    inference(resolution,[status(thm)],[c_81,c_159])).

tff(c_22,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    v1_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_195,plain,(
    ! [A_46,B_47] :
      ( k2_pre_topc(A_46,B_47) = k2_struct_0(A_46)
      | ~ v1_tops_1(B_47,A_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_202,plain,(
    ! [B_47] :
      ( k2_pre_topc('#skF_1',B_47) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_47,'#skF_1')
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_195])).

tff(c_502,plain,(
    ! [B_73] :
      ( k2_pre_topc('#skF_1',B_73) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_73,'#skF_1')
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_202])).

tff(c_539,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_502])).

tff(c_555,plain,(
    k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_539])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_438,plain,(
    ! [A_65,C_66,B_67] :
      ( k2_pre_topc(A_65,k9_subset_1(u1_struct_0(A_65),C_66,B_67)) = k2_pre_topc(A_65,C_66)
      | ~ v3_pre_topc(C_66,A_65)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ v1_tops_1(B_67,A_65)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_443,plain,(
    ! [C_66,B_67] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),C_66,B_67)) = k2_pre_topc('#skF_1',C_66)
      | ~ v3_pre_topc(C_66,'#skF_1')
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ v1_tops_1(B_67,'#skF_1')
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_438])).

tff(c_709,plain,(
    ! [C_84,B_85] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),C_84,B_85)) = k2_pre_topc('#skF_1',C_84)
      | ~ v3_pre_topc(C_84,'#skF_1')
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ v1_tops_1(B_85,'#skF_1')
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_78,c_78,c_443])).

tff(c_740,plain,(
    ! [B_85] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_85)) = k2_pre_topc('#skF_1','#skF_3')
      | ~ v3_pre_topc('#skF_3','#skF_1')
      | ~ v1_tops_1(B_85,'#skF_1')
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_80,c_709])).

tff(c_854,plain,(
    ! [B_94] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_94)) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_94,'#skF_1')
      | ~ m1_subset_1(B_94,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_555,c_740])).

tff(c_897,plain,
    ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_81,c_854])).

tff(c_918,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_167,c_897])).

tff(c_920,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_799,c_918])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.48  
% 3.20/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.49  %$ v3_pre_topc > v1_tops_1 > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.20/1.49  
% 3.20/1.49  %Foreground sorts:
% 3.20/1.49  
% 3.20/1.49  
% 3.20/1.49  %Background operators:
% 3.20/1.49  
% 3.20/1.49  
% 3.20/1.49  %Foreground operators:
% 3.20/1.49  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.20/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.20/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.49  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.20/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.20/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.20/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.20/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.20/1.49  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.20/1.49  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.20/1.49  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.20/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.20/1.49  
% 3.20/1.50  tff(f_89, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v1_tops_1(B, A) & v1_tops_1(C, A)) & v3_pre_topc(C, A)) => v1_tops_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_tops_1)).
% 3.20/1.50  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.20/1.50  tff(f_41, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.20/1.50  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.20/1.50  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.20/1.50  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 3.20/1.50  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.20/1.50  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.20/1.50  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tops_1)).
% 3.20/1.50  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.20/1.50  tff(c_12, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.20/1.50  tff(c_69, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.20/1.50  tff(c_74, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_pre_topc(A_31))), inference(resolution, [status(thm)], [c_12, c_69])).
% 3.20/1.50  tff(c_78, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_74])).
% 3.20/1.50  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.20/1.50  tff(c_81, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_30])).
% 3.20/1.50  tff(c_159, plain, (![A_41, B_42, C_43]: (k9_subset_1(A_41, B_42, C_43)=k3_xboole_0(B_42, C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.20/1.50  tff(c_169, plain, (![B_44]: (k9_subset_1(k2_struct_0('#skF_1'), B_44, '#skF_2')=k3_xboole_0(B_44, '#skF_2'))), inference(resolution, [status(thm)], [c_81, c_159])).
% 3.20/1.50  tff(c_4, plain, (![A_3, B_4, C_5]: (m1_subset_1(k9_subset_1(A_3, B_4, C_5), k1_zfmisc_1(A_3)) | ~m1_subset_1(C_5, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.50  tff(c_175, plain, (![B_44]: (m1_subset_1(k3_xboole_0(B_44, '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_169, c_4])).
% 3.20/1.50  tff(c_181, plain, (![B_44]: (m1_subset_1(k3_xboole_0(B_44, '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_175])).
% 3.20/1.50  tff(c_306, plain, (![B_56, A_57]: (v1_tops_1(B_56, A_57) | k2_pre_topc(A_57, B_56)!=k2_struct_0(A_57) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.20/1.50  tff(c_313, plain, (![B_56]: (v1_tops_1(B_56, '#skF_1') | k2_pre_topc('#skF_1', B_56)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_56, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_306])).
% 3.20/1.50  tff(c_362, plain, (![B_62]: (v1_tops_1(B_62, '#skF_1') | k2_pre_topc('#skF_1', B_62)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_313])).
% 3.20/1.50  tff(c_783, plain, (![B_88]: (v1_tops_1(k3_xboole_0(B_88, '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_xboole_0(B_88, '#skF_2'))!=k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_181, c_362])).
% 3.20/1.50  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.20/1.50  tff(c_86, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.20/1.50  tff(c_101, plain, (![B_34, A_35]: (k1_setfam_1(k2_tarski(B_34, A_35))=k3_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_2, c_86])).
% 3.20/1.50  tff(c_8, plain, (![A_9, B_10]: (k1_setfam_1(k2_tarski(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.20/1.50  tff(c_107, plain, (![B_34, A_35]: (k3_xboole_0(B_34, A_35)=k3_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_101, c_8])).
% 3.20/1.50  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.20/1.50  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_28])).
% 3.20/1.50  tff(c_168, plain, (![B_42]: (k9_subset_1(k2_struct_0('#skF_1'), B_42, '#skF_3')=k3_xboole_0(B_42, '#skF_3'))), inference(resolution, [status(thm)], [c_80, c_159])).
% 3.20/1.50  tff(c_20, plain, (~v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.20/1.50  tff(c_79, plain, (~v1_tops_1(k9_subset_1(k2_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_20])).
% 3.20/1.50  tff(c_221, plain, (~v1_tops_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_79])).
% 3.20/1.50  tff(c_222, plain, (~v1_tops_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_221])).
% 3.20/1.50  tff(c_799, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_783, c_222])).
% 3.20/1.50  tff(c_26, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.20/1.50  tff(c_167, plain, (![B_42]: (k9_subset_1(k2_struct_0('#skF_1'), B_42, '#skF_2')=k3_xboole_0(B_42, '#skF_2'))), inference(resolution, [status(thm)], [c_81, c_159])).
% 3.20/1.50  tff(c_22, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.20/1.50  tff(c_24, plain, (v1_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.20/1.50  tff(c_195, plain, (![A_46, B_47]: (k2_pre_topc(A_46, B_47)=k2_struct_0(A_46) | ~v1_tops_1(B_47, A_46) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.20/1.50  tff(c_202, plain, (![B_47]: (k2_pre_topc('#skF_1', B_47)=k2_struct_0('#skF_1') | ~v1_tops_1(B_47, '#skF_1') | ~m1_subset_1(B_47, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_195])).
% 3.20/1.50  tff(c_502, plain, (![B_73]: (k2_pre_topc('#skF_1', B_73)=k2_struct_0('#skF_1') | ~v1_tops_1(B_73, '#skF_1') | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_202])).
% 3.20/1.50  tff(c_539, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_80, c_502])).
% 3.20/1.50  tff(c_555, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_539])).
% 3.20/1.50  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.20/1.50  tff(c_438, plain, (![A_65, C_66, B_67]: (k2_pre_topc(A_65, k9_subset_1(u1_struct_0(A_65), C_66, B_67))=k2_pre_topc(A_65, C_66) | ~v3_pre_topc(C_66, A_65) | ~m1_subset_1(C_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~v1_tops_1(B_67, A_65) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.20/1.50  tff(c_443, plain, (![C_66, B_67]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), C_66, B_67))=k2_pre_topc('#skF_1', C_66) | ~v3_pre_topc(C_66, '#skF_1') | ~m1_subset_1(C_66, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~v1_tops_1(B_67, '#skF_1') | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_438])).
% 3.20/1.50  tff(c_709, plain, (![C_84, B_85]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), C_84, B_85))=k2_pre_topc('#skF_1', C_84) | ~v3_pre_topc(C_84, '#skF_1') | ~m1_subset_1(C_84, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~v1_tops_1(B_85, '#skF_1') | ~m1_subset_1(B_85, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_78, c_78, c_443])).
% 3.20/1.50  tff(c_740, plain, (![B_85]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_85))=k2_pre_topc('#skF_1', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1') | ~v1_tops_1(B_85, '#skF_1') | ~m1_subset_1(B_85, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_80, c_709])).
% 3.20/1.50  tff(c_854, plain, (![B_94]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_94))=k2_struct_0('#skF_1') | ~v1_tops_1(B_94, '#skF_1') | ~m1_subset_1(B_94, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_555, c_740])).
% 3.20/1.50  tff(c_897, plain, (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_81, c_854])).
% 3.20/1.50  tff(c_918, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_167, c_897])).
% 3.20/1.50  tff(c_920, plain, $false, inference(negUnitSimplification, [status(thm)], [c_799, c_918])).
% 3.20/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.50  
% 3.20/1.50  Inference rules
% 3.20/1.50  ----------------------
% 3.20/1.50  #Ref     : 0
% 3.20/1.50  #Sup     : 208
% 3.20/1.50  #Fact    : 0
% 3.20/1.50  #Define  : 0
% 3.20/1.50  #Split   : 0
% 3.20/1.50  #Chain   : 0
% 3.20/1.50  #Close   : 0
% 3.20/1.50  
% 3.20/1.50  Ordering : KBO
% 3.20/1.50  
% 3.20/1.50  Simplification rules
% 3.20/1.51  ----------------------
% 3.20/1.51  #Subsume      : 4
% 3.20/1.51  #Demod        : 74
% 3.20/1.51  #Tautology    : 78
% 3.20/1.51  #SimpNegUnit  : 3
% 3.20/1.51  #BackRed      : 4
% 3.20/1.51  
% 3.20/1.51  #Partial instantiations: 0
% 3.20/1.51  #Strategies tried      : 1
% 3.20/1.51  
% 3.20/1.51  Timing (in seconds)
% 3.20/1.51  ----------------------
% 3.20/1.51  Preprocessing        : 0.31
% 3.20/1.51  Parsing              : 0.16
% 3.20/1.51  CNF conversion       : 0.02
% 3.20/1.51  Main loop            : 0.42
% 3.20/1.51  Inferencing          : 0.14
% 3.20/1.51  Reduction            : 0.16
% 3.20/1.51  Demodulation         : 0.13
% 3.20/1.51  BG Simplification    : 0.02
% 3.20/1.51  Subsumption          : 0.06
% 3.20/1.51  Abstraction          : 0.03
% 3.20/1.51  MUC search           : 0.00
% 3.20/1.51  Cooper               : 0.00
% 3.20/1.51  Total                : 0.77
% 3.20/1.51  Index Insertion      : 0.00
% 3.20/1.51  Index Deletion       : 0.00
% 3.20/1.51  Index Matching       : 0.00
% 3.20/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
