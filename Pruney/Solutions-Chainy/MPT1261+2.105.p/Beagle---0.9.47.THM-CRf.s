%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:26 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 169 expanded)
%              Number of leaves         :   30 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 348 expanded)
%              Number of equality atoms :   44 (  94 expanded)
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

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_70,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1246,plain,(
    ! [A_127,B_128,C_129] :
      ( k7_subset_1(A_127,B_128,C_129) = k4_xboole_0(B_128,C_129)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1255,plain,(
    ! [C_129] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_129) = k4_xboole_0('#skF_2',C_129) ),
    inference(resolution,[status(thm)],[c_32,c_1246])).

tff(c_38,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_103,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_488,plain,(
    ! [B_72,A_73] :
      ( v4_pre_topc(B_72,A_73)
      | k2_pre_topc(A_73,B_72) != B_72
      | ~ v2_pre_topc(A_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_505,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_488])).

tff(c_516,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_505])).

tff(c_517,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_516])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_148,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_44])).

tff(c_138,plain,(
    ! [A_48,B_49,C_50] :
      ( k7_subset_1(A_48,B_49,C_50) = k4_xboole_0(B_49,C_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_178,plain,(
    ! [C_51] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_51) = k4_xboole_0('#skF_2',C_51) ),
    inference(resolution,[status(thm)],[c_32,c_138])).

tff(c_196,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_178])).

tff(c_346,plain,(
    ! [B_61,A_62,C_63] :
      ( k7_subset_1(B_61,A_62,C_63) = k4_xboole_0(A_62,C_63)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(resolution,[status(thm)],[c_20,c_138])).

tff(c_379,plain,(
    ! [B_67,C_68] : k7_subset_1(B_67,B_67,C_68) = k4_xboole_0(B_67,C_68) ),
    inference(resolution,[status(thm)],[c_8,c_346])).

tff(c_124,plain,(
    ! [A_42,B_43,C_44] :
      ( m1_subset_1(k7_subset_1(A_42,B_43,C_44),k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_128,plain,(
    ! [A_42,B_43,C_44] :
      ( r1_tarski(k7_subset_1(A_42,B_43,C_44),A_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(resolution,[status(thm)],[c_124,c_18])).

tff(c_394,plain,(
    ! [B_69,C_70] :
      ( r1_tarski(k4_xboole_0(B_69,C_70),B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(B_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_128])).

tff(c_404,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_394])).

tff(c_409,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_404])).

tff(c_439,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_409])).

tff(c_443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_439])).

tff(c_444,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_404])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_467,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_444,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_471,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_2])).

tff(c_557,plain,(
    ! [A_75,B_76] :
      ( k4_subset_1(u1_struct_0(A_75),B_76,k2_tops_1(A_75,B_76)) = k2_pre_topc(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_569,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_557])).

tff(c_580,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_569])).

tff(c_152,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_128])).

tff(c_159,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_152])).

tff(c_363,plain,(
    ! [A_64,B_65,C_66] :
      ( k4_subset_1(A_64,B_65,C_66) = k2_xboole_0(B_65,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_64))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1101,plain,(
    ! [B_110,B_111,A_112] :
      ( k4_subset_1(B_110,B_111,A_112) = k2_xboole_0(B_111,A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(B_110))
      | ~ r1_tarski(A_112,B_110) ) ),
    inference(resolution,[status(thm)],[c_20,c_363])).

tff(c_1177,plain,(
    ! [A_116] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_116) = k2_xboole_0('#skF_2',A_116)
      | ~ r1_tarski(A_116,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_32,c_1101])).

tff(c_1187,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_159,c_1177])).

tff(c_1205,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_580,c_1187])).

tff(c_1207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_517,c_1205])).

tff(c_1208,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1256,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1255,c_1208])).

tff(c_1209,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1357,plain,(
    ! [A_142,B_143] :
      ( k2_pre_topc(A_142,B_143) = B_143
      | ~ v4_pre_topc(B_143,A_142)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1371,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1357])).

tff(c_1379,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1209,c_1371])).

tff(c_1845,plain,(
    ! [A_190,B_191] :
      ( k7_subset_1(u1_struct_0(A_190),k2_pre_topc(A_190,B_191),k1_tops_1(A_190,B_191)) = k2_tops_1(A_190,B_191)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1863,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1379,c_1845])).

tff(c_1867,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1255,c_1863])).

tff(c_1869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1256,c_1867])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:08:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.62  
% 3.53/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.62  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.53/1.62  
% 3.53/1.62  %Foreground sorts:
% 3.53/1.62  
% 3.53/1.62  
% 3.53/1.62  %Background operators:
% 3.53/1.62  
% 3.53/1.62  
% 3.53/1.62  %Foreground operators:
% 3.53/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.53/1.62  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.53/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.53/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.62  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.53/1.62  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.53/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.62  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.53/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.62  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.53/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.53/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.53/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.53/1.62  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.53/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.62  
% 3.53/1.64  tff(f_104, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 3.53/1.64  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.53/1.64  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.53/1.64  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.53/1.64  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.53/1.64  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 3.53/1.64  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.53/1.64  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.53/1.64  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 3.53/1.64  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.53/1.64  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 3.53/1.64  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.53/1.64  tff(c_1246, plain, (![A_127, B_128, C_129]: (k7_subset_1(A_127, B_128, C_129)=k4_xboole_0(B_128, C_129) | ~m1_subset_1(B_128, k1_zfmisc_1(A_127)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.53/1.64  tff(c_1255, plain, (![C_129]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_129)=k4_xboole_0('#skF_2', C_129))), inference(resolution, [status(thm)], [c_32, c_1246])).
% 3.53/1.64  tff(c_38, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.53/1.64  tff(c_103, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 3.53/1.64  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.53/1.64  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.53/1.64  tff(c_488, plain, (![B_72, A_73]: (v4_pre_topc(B_72, A_73) | k2_pre_topc(A_73, B_72)!=B_72 | ~v2_pre_topc(A_73) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.53/1.64  tff(c_505, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_488])).
% 3.53/1.64  tff(c_516, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_505])).
% 3.53/1.64  tff(c_517, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_103, c_516])).
% 3.53/1.64  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.53/1.64  tff(c_20, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.53/1.64  tff(c_44, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.53/1.64  tff(c_148, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_103, c_44])).
% 3.53/1.64  tff(c_138, plain, (![A_48, B_49, C_50]: (k7_subset_1(A_48, B_49, C_50)=k4_xboole_0(B_49, C_50) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.53/1.64  tff(c_178, plain, (![C_51]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_51)=k4_xboole_0('#skF_2', C_51))), inference(resolution, [status(thm)], [c_32, c_138])).
% 3.53/1.64  tff(c_196, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_148, c_178])).
% 3.53/1.64  tff(c_346, plain, (![B_61, A_62, C_63]: (k7_subset_1(B_61, A_62, C_63)=k4_xboole_0(A_62, C_63) | ~r1_tarski(A_62, B_61))), inference(resolution, [status(thm)], [c_20, c_138])).
% 3.53/1.64  tff(c_379, plain, (![B_67, C_68]: (k7_subset_1(B_67, B_67, C_68)=k4_xboole_0(B_67, C_68))), inference(resolution, [status(thm)], [c_8, c_346])).
% 3.53/1.64  tff(c_124, plain, (![A_42, B_43, C_44]: (m1_subset_1(k7_subset_1(A_42, B_43, C_44), k1_zfmisc_1(A_42)) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.53/1.64  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.53/1.64  tff(c_128, plain, (![A_42, B_43, C_44]: (r1_tarski(k7_subset_1(A_42, B_43, C_44), A_42) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(resolution, [status(thm)], [c_124, c_18])).
% 3.53/1.64  tff(c_394, plain, (![B_69, C_70]: (r1_tarski(k4_xboole_0(B_69, C_70), B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(B_69)))), inference(superposition, [status(thm), theory('equality')], [c_379, c_128])).
% 3.53/1.64  tff(c_404, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_196, c_394])).
% 3.53/1.64  tff(c_409, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_404])).
% 3.53/1.64  tff(c_439, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_409])).
% 3.53/1.64  tff(c_443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_439])).
% 3.53/1.64  tff(c_444, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_404])).
% 3.53/1.64  tff(c_10, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.53/1.64  tff(c_467, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_444, c_10])).
% 3.53/1.64  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.53/1.64  tff(c_471, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_467, c_2])).
% 3.53/1.64  tff(c_557, plain, (![A_75, B_76]: (k4_subset_1(u1_struct_0(A_75), B_76, k2_tops_1(A_75, B_76))=k2_pre_topc(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.53/1.64  tff(c_569, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_557])).
% 3.53/1.64  tff(c_580, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_569])).
% 3.53/1.64  tff(c_152, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_148, c_128])).
% 3.53/1.64  tff(c_159, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_152])).
% 3.53/1.64  tff(c_363, plain, (![A_64, B_65, C_66]: (k4_subset_1(A_64, B_65, C_66)=k2_xboole_0(B_65, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(A_64)) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.53/1.64  tff(c_1101, plain, (![B_110, B_111, A_112]: (k4_subset_1(B_110, B_111, A_112)=k2_xboole_0(B_111, A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(B_110)) | ~r1_tarski(A_112, B_110))), inference(resolution, [status(thm)], [c_20, c_363])).
% 3.53/1.64  tff(c_1177, plain, (![A_116]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_116)=k2_xboole_0('#skF_2', A_116) | ~r1_tarski(A_116, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_32, c_1101])).
% 3.53/1.64  tff(c_1187, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_159, c_1177])).
% 3.53/1.64  tff(c_1205, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_471, c_580, c_1187])).
% 3.53/1.64  tff(c_1207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_517, c_1205])).
% 3.53/1.64  tff(c_1208, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 3.53/1.64  tff(c_1256, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1255, c_1208])).
% 3.53/1.64  tff(c_1209, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_38])).
% 3.53/1.64  tff(c_1357, plain, (![A_142, B_143]: (k2_pre_topc(A_142, B_143)=B_143 | ~v4_pre_topc(B_143, A_142) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.53/1.64  tff(c_1371, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1357])).
% 3.53/1.64  tff(c_1379, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1209, c_1371])).
% 3.53/1.64  tff(c_1845, plain, (![A_190, B_191]: (k7_subset_1(u1_struct_0(A_190), k2_pre_topc(A_190, B_191), k1_tops_1(A_190, B_191))=k2_tops_1(A_190, B_191) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.53/1.64  tff(c_1863, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1379, c_1845])).
% 3.53/1.64  tff(c_1867, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1255, c_1863])).
% 3.53/1.64  tff(c_1869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1256, c_1867])).
% 3.53/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.64  
% 3.53/1.64  Inference rules
% 3.53/1.64  ----------------------
% 3.53/1.64  #Ref     : 0
% 3.53/1.64  #Sup     : 422
% 3.53/1.64  #Fact    : 0
% 3.53/1.64  #Define  : 0
% 3.53/1.64  #Split   : 10
% 3.53/1.64  #Chain   : 0
% 3.53/1.64  #Close   : 0
% 3.53/1.64  
% 3.53/1.64  Ordering : KBO
% 3.53/1.64  
% 3.53/1.64  Simplification rules
% 3.53/1.64  ----------------------
% 3.53/1.64  #Subsume      : 6
% 3.53/1.64  #Demod        : 254
% 3.53/1.64  #Tautology    : 190
% 3.53/1.64  #SimpNegUnit  : 7
% 3.53/1.64  #BackRed      : 3
% 3.53/1.64  
% 3.53/1.64  #Partial instantiations: 0
% 3.53/1.64  #Strategies tried      : 1
% 3.53/1.64  
% 3.53/1.64  Timing (in seconds)
% 3.53/1.64  ----------------------
% 3.87/1.64  Preprocessing        : 0.32
% 3.87/1.64  Parsing              : 0.17
% 3.87/1.64  CNF conversion       : 0.02
% 3.87/1.64  Main loop            : 0.57
% 3.87/1.64  Inferencing          : 0.20
% 3.87/1.64  Reduction            : 0.20
% 3.87/1.64  Demodulation         : 0.15
% 3.87/1.64  BG Simplification    : 0.03
% 3.87/1.64  Subsumption          : 0.09
% 3.87/1.64  Abstraction          : 0.03
% 3.87/1.64  MUC search           : 0.00
% 3.87/1.64  Cooper               : 0.00
% 3.87/1.64  Total                : 0.93
% 3.87/1.64  Index Insertion      : 0.00
% 3.87/1.64  Index Deletion       : 0.00
% 3.87/1.64  Index Matching       : 0.00
% 3.87/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
