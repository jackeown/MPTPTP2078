%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:29 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 112 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :  108 ( 236 expanded)
%              Number of equality atoms :   43 (  72 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_351,plain,(
    ! [A_72,B_73,C_74] :
      ( k7_subset_1(A_72,B_73,C_74) = k4_xboole_0(B_73,C_74)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_354,plain,(
    ! [C_74] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_74) = k4_xboole_0('#skF_2',C_74) ),
    inference(resolution,[status(thm)],[c_22,c_351])).

tff(c_34,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_107,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_28,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_134,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_28])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_200,plain,(
    ! [B_46,A_47] :
      ( v4_pre_topc(B_46,A_47)
      | k2_pre_topc(A_47,B_46) != B_46
      | ~ v2_pre_topc(A_47)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_206,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_200])).

tff(c_210,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_206])).

tff(c_211,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_210])).

tff(c_243,plain,(
    ! [A_50,B_51] :
      ( k4_subset_1(u1_struct_0(A_50),B_51,k2_tops_1(A_50,B_51)) = k2_pre_topc(A_50,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_247,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_243])).

tff(c_251,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_247])).

tff(c_114,plain,(
    ! [A_35,B_36,C_37] :
      ( k7_subset_1(A_35,B_36,C_37) = k4_xboole_0(B_36,C_37)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_118,plain,(
    ! [C_38] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_38) = k4_xboole_0('#skF_2',C_38) ),
    inference(resolution,[status(thm)],[c_22,c_114])).

tff(c_124,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_107])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [A_29,B_30] :
      ( k2_xboole_0(A_29,B_30) = B_30
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_31,B_32] : k2_xboole_0(k4_xboole_0(A_31,B_32),A_31) = A_31 ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_80,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = A_31 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_2])).

tff(c_138,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_80])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k2_tops_1(A_16,B_17),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_193,plain,(
    ! [A_43,B_44,C_45] :
      ( k4_subset_1(A_43,B_44,C_45) = k2_xboole_0(B_44,C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(A_43))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_321,plain,(
    ! [A_68,B_69,B_70] :
      ( k4_subset_1(u1_struct_0(A_68),B_69,k2_tops_1(A_68,B_70)) = k2_xboole_0(B_69,k2_tops_1(A_68,B_70))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_16,c_193])).

tff(c_325,plain,(
    ! [B_70] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_70)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_70))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_321])).

tff(c_330,plain,(
    ! [B_71] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_71)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_71))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_325])).

tff(c_337,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_330])).

tff(c_342,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_138,c_337])).

tff(c_344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_342])).

tff(c_346,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_355,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_346])).

tff(c_345,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_369,plain,(
    ! [A_78,B_79] :
      ( k2_pre_topc(A_78,B_79) = B_79
      | ~ v4_pre_topc(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_375,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_369])).

tff(c_379,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_345,c_375])).

tff(c_445,plain,(
    ! [A_89,B_90] :
      ( k7_subset_1(u1_struct_0(A_89),k2_pre_topc(A_89,B_90),k1_tops_1(A_89,B_90)) = k2_tops_1(A_89,B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_454,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_445])).

tff(c_458,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_354,c_454])).

tff(c_460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_355,c_458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.33  
% 2.14/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.33  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.56/1.33  
% 2.56/1.33  %Foreground sorts:
% 2.56/1.33  
% 2.56/1.33  
% 2.56/1.33  %Background operators:
% 2.56/1.33  
% 2.56/1.33  
% 2.56/1.33  %Foreground operators:
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.56/1.33  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.56/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.56/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.33  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.56/1.33  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.56/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.33  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.56/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.56/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.33  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.56/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.56/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.56/1.33  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.56/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.33  
% 2.56/1.35  tff(f_90, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 2.56/1.35  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.56/1.35  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.56/1.35  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 2.56/1.35  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.56/1.35  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.56/1.35  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.56/1.35  tff(f_64, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.56/1.35  tff(f_39, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.56/1.35  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 2.56/1.35  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.56/1.35  tff(c_351, plain, (![A_72, B_73, C_74]: (k7_subset_1(A_72, B_73, C_74)=k4_xboole_0(B_73, C_74) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.56/1.35  tff(c_354, plain, (![C_74]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_74)=k4_xboole_0('#skF_2', C_74))), inference(resolution, [status(thm)], [c_22, c_351])).
% 2.56/1.35  tff(c_34, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.56/1.35  tff(c_107, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_34])).
% 2.56/1.35  tff(c_28, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.56/1.35  tff(c_134, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_28])).
% 2.56/1.35  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.56/1.35  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.56/1.35  tff(c_200, plain, (![B_46, A_47]: (v4_pre_topc(B_46, A_47) | k2_pre_topc(A_47, B_46)!=B_46 | ~v2_pre_topc(A_47) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.56/1.35  tff(c_206, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_200])).
% 2.56/1.35  tff(c_210, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_206])).
% 2.56/1.35  tff(c_211, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_134, c_210])).
% 2.56/1.35  tff(c_243, plain, (![A_50, B_51]: (k4_subset_1(u1_struct_0(A_50), B_51, k2_tops_1(A_50, B_51))=k2_pre_topc(A_50, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.56/1.35  tff(c_247, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_243])).
% 2.56/1.35  tff(c_251, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_247])).
% 2.56/1.35  tff(c_114, plain, (![A_35, B_36, C_37]: (k7_subset_1(A_35, B_36, C_37)=k4_xboole_0(B_36, C_37) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.56/1.35  tff(c_118, plain, (![C_38]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_38)=k4_xboole_0('#skF_2', C_38))), inference(resolution, [status(thm)], [c_22, c_114])).
% 2.56/1.35  tff(c_124, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_118, c_107])).
% 2.56/1.35  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.56/1.35  tff(c_69, plain, (![A_29, B_30]: (k2_xboole_0(A_29, B_30)=B_30 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.35  tff(c_74, plain, (![A_31, B_32]: (k2_xboole_0(k4_xboole_0(A_31, B_32), A_31)=A_31)), inference(resolution, [status(thm)], [c_6, c_69])).
% 2.56/1.35  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.56/1.35  tff(c_80, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k4_xboole_0(A_31, B_32))=A_31)), inference(superposition, [status(thm), theory('equality')], [c_74, c_2])).
% 2.56/1.35  tff(c_138, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_124, c_80])).
% 2.56/1.35  tff(c_16, plain, (![A_16, B_17]: (m1_subset_1(k2_tops_1(A_16, B_17), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.56/1.35  tff(c_193, plain, (![A_43, B_44, C_45]: (k4_subset_1(A_43, B_44, C_45)=k2_xboole_0(B_44, C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(A_43)) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.56/1.35  tff(c_321, plain, (![A_68, B_69, B_70]: (k4_subset_1(u1_struct_0(A_68), B_69, k2_tops_1(A_68, B_70))=k2_xboole_0(B_69, k2_tops_1(A_68, B_70)) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_16, c_193])).
% 2.56/1.35  tff(c_325, plain, (![B_70]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_70))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_70)) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_321])).
% 2.56/1.35  tff(c_330, plain, (![B_71]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_71))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_71)) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_325])).
% 2.56/1.35  tff(c_337, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_330])).
% 2.56/1.35  tff(c_342, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_251, c_138, c_337])).
% 2.56/1.35  tff(c_344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_342])).
% 2.56/1.35  tff(c_346, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 2.56/1.35  tff(c_355, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_354, c_346])).
% 2.56/1.35  tff(c_345, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 2.56/1.35  tff(c_369, plain, (![A_78, B_79]: (k2_pre_topc(A_78, B_79)=B_79 | ~v4_pre_topc(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.56/1.35  tff(c_375, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_369])).
% 2.56/1.35  tff(c_379, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_345, c_375])).
% 2.56/1.35  tff(c_445, plain, (![A_89, B_90]: (k7_subset_1(u1_struct_0(A_89), k2_pre_topc(A_89, B_90), k1_tops_1(A_89, B_90))=k2_tops_1(A_89, B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.56/1.35  tff(c_454, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_379, c_445])).
% 2.56/1.35  tff(c_458, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_354, c_454])).
% 2.56/1.35  tff(c_460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_355, c_458])).
% 2.56/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.35  
% 2.56/1.35  Inference rules
% 2.56/1.35  ----------------------
% 2.56/1.35  #Ref     : 0
% 2.56/1.35  #Sup     : 102
% 2.56/1.35  #Fact    : 0
% 2.56/1.35  #Define  : 0
% 2.56/1.35  #Split   : 2
% 2.56/1.35  #Chain   : 0
% 2.56/1.35  #Close   : 0
% 2.56/1.35  
% 2.56/1.35  Ordering : KBO
% 2.56/1.35  
% 2.56/1.35  Simplification rules
% 2.56/1.35  ----------------------
% 2.56/1.35  #Subsume      : 6
% 2.56/1.35  #Demod        : 43
% 2.56/1.35  #Tautology    : 60
% 2.56/1.35  #SimpNegUnit  : 3
% 2.56/1.35  #BackRed      : 1
% 2.56/1.35  
% 2.56/1.35  #Partial instantiations: 0
% 2.56/1.35  #Strategies tried      : 1
% 2.56/1.35  
% 2.56/1.35  Timing (in seconds)
% 2.56/1.35  ----------------------
% 2.56/1.35  Preprocessing        : 0.30
% 2.56/1.35  Parsing              : 0.16
% 2.56/1.35  CNF conversion       : 0.02
% 2.56/1.35  Main loop            : 0.27
% 2.56/1.35  Inferencing          : 0.10
% 2.56/1.35  Reduction            : 0.09
% 2.56/1.35  Demodulation         : 0.07
% 2.56/1.35  BG Simplification    : 0.02
% 2.56/1.35  Subsumption          : 0.05
% 2.56/1.35  Abstraction          : 0.02
% 2.56/1.35  MUC search           : 0.00
% 2.56/1.35  Cooper               : 0.00
% 2.56/1.35  Total                : 0.61
% 2.56/1.35  Index Insertion      : 0.00
% 2.56/1.35  Index Deletion       : 0.00
% 2.56/1.35  Index Matching       : 0.00
% 2.56/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
