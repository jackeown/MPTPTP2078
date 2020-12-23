%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:36 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 118 expanded)
%              Number of leaves         :   33 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :  111 ( 239 expanded)
%              Number of equality atoms :   46 (  74 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_644,plain,(
    ! [A_100,B_101,C_102] :
      ( k7_subset_1(A_100,B_101,C_102) = k4_xboole_0(B_101,C_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_647,plain,(
    ! [C_102] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_102) = k4_xboole_0('#skF_2',C_102) ),
    inference(resolution,[status(thm)],[c_30,c_644])).

tff(c_36,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_86,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_380,plain,(
    ! [B_64,A_65] :
      ( v4_pre_topc(B_64,A_65)
      | k2_pre_topc(A_65,B_64) != B_64
      | ~ v2_pre_topc(A_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_386,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_380])).

tff(c_390,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_386])).

tff(c_391,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_390])).

tff(c_393,plain,(
    ! [A_68,B_69] :
      ( k4_subset_1(u1_struct_0(A_68),B_69,k2_tops_1(A_68,B_69)) = k2_pre_topc(A_68,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_397,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_393])).

tff(c_401,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_397])).

tff(c_222,plain,(
    ! [A_50,B_51,C_52] :
      ( k7_subset_1(A_50,B_51,C_52) = k4_xboole_0(B_51,C_52)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_226,plain,(
    ! [C_53] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_53) = k4_xboole_0('#skF_2',C_53) ),
    inference(resolution,[status(thm)],[c_30,c_222])).

tff(c_42,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_207,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_42])).

tff(c_232,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_207])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    ! [A_6,B_7] : k4_xboole_0(k4_xboole_0(A_6,B_7),A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_54])).

tff(c_137,plain,(
    ! [A_43,B_44] : k2_xboole_0(A_43,k4_xboole_0(B_44,A_43)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_152,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k2_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_137])).

tff(c_157,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_152])).

tff(c_244,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_157])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_tops_1(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_356,plain,(
    ! [A_60,B_61,C_62] :
      ( k4_subset_1(A_60,B_61,C_62) = k2_xboole_0(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_487,plain,(
    ! [A_87,B_88,B_89] :
      ( k4_subset_1(u1_struct_0(A_87),B_88,k2_tops_1(A_87,B_89)) = k2_xboole_0(B_88,k2_tops_1(A_87,B_89))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_22,c_356])).

tff(c_491,plain,(
    ! [B_89] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_89)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_89))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_487])).

tff(c_496,plain,(
    ! [B_90] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_90)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_90))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_491])).

tff(c_503,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_496])).

tff(c_508,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_244,c_503])).

tff(c_510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_508])).

tff(c_511,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_652,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_511])).

tff(c_512,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_662,plain,(
    ! [A_106,B_107] :
      ( k2_pre_topc(A_106,B_107) = B_107
      | ~ v4_pre_topc(B_107,A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_668,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_662])).

tff(c_672,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_512,c_668])).

tff(c_751,plain,(
    ! [A_121,B_122] :
      ( k7_subset_1(u1_struct_0(A_121),k2_pre_topc(A_121,B_122),k1_tops_1(A_121,B_122)) = k2_tops_1(A_121,B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_760,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_751])).

tff(c_764,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_647,c_760])).

tff(c_766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_652,c_764])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.47  
% 2.94/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.48  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.94/1.48  
% 2.94/1.48  %Foreground sorts:
% 2.94/1.48  
% 2.94/1.48  
% 2.94/1.48  %Background operators:
% 2.94/1.48  
% 2.94/1.48  
% 2.94/1.48  %Foreground operators:
% 2.94/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.94/1.48  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.94/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.94/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.94/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.48  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.94/1.48  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.94/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.48  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.94/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.94/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.48  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.94/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.94/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.94/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.94/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.94/1.48  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.94/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.48  
% 2.94/1.49  tff(f_102, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 2.94/1.49  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.94/1.49  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.94/1.49  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 2.94/1.49  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.94/1.49  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.94/1.49  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.94/1.49  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.94/1.49  tff(f_68, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.94/1.49  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.94/1.49  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 2.94/1.49  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.94/1.49  tff(c_644, plain, (![A_100, B_101, C_102]: (k7_subset_1(A_100, B_101, C_102)=k4_xboole_0(B_101, C_102) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.94/1.49  tff(c_647, plain, (![C_102]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_102)=k4_xboole_0('#skF_2', C_102))), inference(resolution, [status(thm)], [c_30, c_644])).
% 2.94/1.49  tff(c_36, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.94/1.49  tff(c_86, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 2.94/1.49  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.94/1.49  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.94/1.49  tff(c_380, plain, (![B_64, A_65]: (v4_pre_topc(B_64, A_65) | k2_pre_topc(A_65, B_64)!=B_64 | ~v2_pre_topc(A_65) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.94/1.49  tff(c_386, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_380])).
% 2.94/1.49  tff(c_390, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_386])).
% 2.94/1.49  tff(c_391, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_86, c_390])).
% 2.94/1.49  tff(c_393, plain, (![A_68, B_69]: (k4_subset_1(u1_struct_0(A_68), B_69, k2_tops_1(A_68, B_69))=k2_pre_topc(A_68, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.94/1.49  tff(c_397, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_393])).
% 2.94/1.49  tff(c_401, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_397])).
% 2.94/1.49  tff(c_222, plain, (![A_50, B_51, C_52]: (k7_subset_1(A_50, B_51, C_52)=k4_xboole_0(B_51, C_52) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.94/1.49  tff(c_226, plain, (![C_53]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_53)=k4_xboole_0('#skF_2', C_53))), inference(resolution, [status(thm)], [c_30, c_222])).
% 2.94/1.49  tff(c_42, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.94/1.49  tff(c_207, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_86, c_42])).
% 2.94/1.49  tff(c_232, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_226, c_207])).
% 2.94/1.49  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.94/1.49  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.94/1.49  tff(c_54, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.94/1.49  tff(c_62, plain, (![A_6, B_7]: (k4_xboole_0(k4_xboole_0(A_6, B_7), A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_54])).
% 2.94/1.49  tff(c_137, plain, (![A_43, B_44]: (k2_xboole_0(A_43, k4_xboole_0(B_44, A_43))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.94/1.49  tff(c_152, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k2_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_62, c_137])).
% 2.94/1.49  tff(c_157, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(A_6, B_7))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_152])).
% 2.94/1.49  tff(c_244, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_232, c_157])).
% 2.94/1.49  tff(c_22, plain, (![A_19, B_20]: (m1_subset_1(k2_tops_1(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.94/1.49  tff(c_356, plain, (![A_60, B_61, C_62]: (k4_subset_1(A_60, B_61, C_62)=k2_xboole_0(B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.94/1.49  tff(c_487, plain, (![A_87, B_88, B_89]: (k4_subset_1(u1_struct_0(A_87), B_88, k2_tops_1(A_87, B_89))=k2_xboole_0(B_88, k2_tops_1(A_87, B_89)) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_22, c_356])).
% 2.94/1.49  tff(c_491, plain, (![B_89]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_89))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_89)) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_487])).
% 2.94/1.49  tff(c_496, plain, (![B_90]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_90))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_90)) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_491])).
% 2.94/1.49  tff(c_503, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_496])).
% 2.94/1.49  tff(c_508, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_401, c_244, c_503])).
% 2.94/1.49  tff(c_510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_391, c_508])).
% 2.94/1.49  tff(c_511, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 2.94/1.49  tff(c_652, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_647, c_511])).
% 2.94/1.49  tff(c_512, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 2.94/1.49  tff(c_662, plain, (![A_106, B_107]: (k2_pre_topc(A_106, B_107)=B_107 | ~v4_pre_topc(B_107, A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.94/1.49  tff(c_668, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_662])).
% 2.94/1.49  tff(c_672, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_512, c_668])).
% 2.94/1.49  tff(c_751, plain, (![A_121, B_122]: (k7_subset_1(u1_struct_0(A_121), k2_pre_topc(A_121, B_122), k1_tops_1(A_121, B_122))=k2_tops_1(A_121, B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.94/1.49  tff(c_760, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_672, c_751])).
% 2.94/1.49  tff(c_764, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_647, c_760])).
% 2.94/1.49  tff(c_766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_652, c_764])).
% 2.94/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.49  
% 2.94/1.49  Inference rules
% 2.94/1.49  ----------------------
% 2.94/1.49  #Ref     : 0
% 2.94/1.49  #Sup     : 182
% 2.94/1.49  #Fact    : 0
% 2.94/1.49  #Define  : 0
% 2.94/1.49  #Split   : 2
% 2.94/1.49  #Chain   : 0
% 2.94/1.49  #Close   : 0
% 2.94/1.49  
% 2.94/1.49  Ordering : KBO
% 2.94/1.49  
% 2.94/1.49  Simplification rules
% 2.94/1.49  ----------------------
% 2.94/1.49  #Subsume      : 1
% 2.94/1.49  #Demod        : 95
% 2.94/1.49  #Tautology    : 131
% 2.94/1.49  #SimpNegUnit  : 4
% 2.94/1.49  #BackRed      : 1
% 2.94/1.49  
% 2.94/1.49  #Partial instantiations: 0
% 2.94/1.49  #Strategies tried      : 1
% 2.94/1.49  
% 2.94/1.49  Timing (in seconds)
% 2.94/1.49  ----------------------
% 3.10/1.50  Preprocessing        : 0.33
% 3.10/1.50  Parsing              : 0.19
% 3.10/1.50  CNF conversion       : 0.02
% 3.10/1.50  Main loop            : 0.32
% 3.10/1.50  Inferencing          : 0.12
% 3.10/1.50  Reduction            : 0.10
% 3.10/1.50  Demodulation         : 0.07
% 3.10/1.50  BG Simplification    : 0.02
% 3.10/1.50  Subsumption          : 0.05
% 3.10/1.50  Abstraction          : 0.02
% 3.10/1.50  MUC search           : 0.00
% 3.10/1.50  Cooper               : 0.00
% 3.10/1.50  Total                : 0.69
% 3.10/1.50  Index Insertion      : 0.00
% 3.10/1.50  Index Deletion       : 0.00
% 3.10/1.50  Index Matching       : 0.00
% 3.10/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
