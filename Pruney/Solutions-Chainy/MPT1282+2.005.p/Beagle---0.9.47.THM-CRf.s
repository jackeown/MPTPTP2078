%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:20 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 261 expanded)
%              Number of leaves         :   20 ( 103 expanded)
%              Depth                    :   12
%              Number of atoms          :  114 ( 698 expanded)
%              Number of equality atoms :   40 ( 238 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > m1_subset_1 > l1_pre_topc > k7_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v6_tops_1(B,A)
             => ( k2_tops_1(A,B) = k2_tops_1(A,k2_pre_topc(A,B))
                & k2_tops_1(A,k2_pre_topc(A,B)) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tops_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_14,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_62,plain,(
    k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    v6_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_53,plain,(
    ! [A_20,B_21] :
      ( k1_tops_1(A_20,k2_pre_topc(A_20,B_21)) = B_21
      | ~ v6_tops_1(B_21,A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_57,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ v6_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_53])).

tff(c_61,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k2_pre_topc(A_1,B_2),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( k2_pre_topc(A_16,k2_pre_topc(A_16,B_17)) = k2_pre_topc(A_16,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_22])).

tff(c_30,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_26])).

tff(c_67,plain,(
    ! [B_22,A_23] :
      ( v6_tops_1(B_22,A_23)
      | k1_tops_1(A_23,k2_pre_topc(A_23,B_22)) != B_22
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_71,plain,
    ( v6_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) != k2_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_67])).

tff(c_76,plain,
    ( v6_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_61,c_71])).

tff(c_77,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_80,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_77])).

tff(c_84,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_80])).

tff(c_86,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k1_tops_1(A_11,k1_tops_1(A_11,B_12)) = k1_tops_1(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_114,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_12])).

tff(c_122,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_61,c_61,c_114])).

tff(c_10,plain,(
    ! [A_8,B_10] :
      ( k7_subset_1(u1_struct_0(A_8),k2_pre_topc(A_8,B_10),k1_tops_1(A_8,B_10)) = k2_tops_1(A_8,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_130,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_10])).

tff(c_134,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_130])).

tff(c_87,plain,(
    ! [A_24,B_25] :
      ( k7_subset_1(u1_struct_0(A_24),k2_pre_topc(A_24,B_25),k1_tops_1(A_24,B_25)) = k2_tops_1(A_24,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_102,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_87])).

tff(c_110,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_61,c_102])).

tff(c_138,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_110])).

tff(c_144,plain,(
    k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_138])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_144])).

tff(c_148,plain,(
    k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_147,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_157,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_147])).

tff(c_158,plain,(
    ! [B_26,A_27] :
      ( v6_tops_1(B_26,A_27)
      | k1_tops_1(A_27,k2_pre_topc(A_27,B_26)) != B_26
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_162,plain,
    ( v6_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) != k2_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_158])).

tff(c_167,plain,
    ( v6_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_61,c_162])).

tff(c_168,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_171,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_168])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_171])).

tff(c_177,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_181,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_177,c_12])).

tff(c_189,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_61,c_61,c_181])).

tff(c_200,plain,(
    ! [A_28,B_29] :
      ( k7_subset_1(u1_struct_0(A_28),k2_pre_topc(A_28,B_29),k1_tops_1(A_28,B_29)) = k2_tops_1(A_28,B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_209,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_200])).

tff(c_219,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_209])).

tff(c_221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:04:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.26  
% 2.04/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.26  %$ v6_tops_1 > m1_subset_1 > l1_pre_topc > k7_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.04/1.26  
% 2.04/1.26  %Foreground sorts:
% 2.04/1.26  
% 2.04/1.26  
% 2.04/1.26  %Background operators:
% 2.04/1.26  
% 2.04/1.26  
% 2.04/1.26  %Foreground operators:
% 2.04/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.26  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 2.04/1.26  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.04/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.04/1.26  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.04/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.26  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.04/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.04/1.26  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.04/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.26  
% 2.17/1.28  tff(f_71, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) => ((k2_tops_1(A, B) = k2_tops_1(A, k2_pre_topc(A, B))) & (k2_tops_1(A, k2_pre_topc(A, B)) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tops_1)).
% 2.17/1.28  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tops_1)).
% 2.17/1.28  tff(f_31, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.17/1.28  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 2.17/1.28  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 2.17/1.28  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 2.17/1.28  tff(c_14, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.17/1.28  tff(c_62, plain, (k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_14])).
% 2.17/1.28  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.17/1.28  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.17/1.28  tff(c_16, plain, (v6_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.17/1.28  tff(c_53, plain, (![A_20, B_21]: (k1_tops_1(A_20, k2_pre_topc(A_20, B_21))=B_21 | ~v6_tops_1(B_21, A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.28  tff(c_57, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~v6_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_53])).
% 2.17/1.28  tff(c_61, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_57])).
% 2.17/1.28  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k2_pre_topc(A_1, B_2), k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.28  tff(c_22, plain, (![A_16, B_17]: (k2_pre_topc(A_16, k2_pre_topc(A_16, B_17))=k2_pre_topc(A_16, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.28  tff(c_26, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_22])).
% 2.17/1.28  tff(c_30, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_26])).
% 2.17/1.28  tff(c_67, plain, (![B_22, A_23]: (v6_tops_1(B_22, A_23) | k1_tops_1(A_23, k2_pre_topc(A_23, B_22))!=B_22 | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.28  tff(c_71, plain, (v6_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_67])).
% 2.17/1.28  tff(c_76, plain, (v6_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_61, c_71])).
% 2.17/1.28  tff(c_77, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_76])).
% 2.17/1.28  tff(c_80, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_77])).
% 2.17/1.28  tff(c_84, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_80])).
% 2.17/1.28  tff(c_86, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_76])).
% 2.17/1.28  tff(c_12, plain, (![A_11, B_12]: (k1_tops_1(A_11, k1_tops_1(A_11, B_12))=k1_tops_1(A_11, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.17/1.28  tff(c_114, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_86, c_12])).
% 2.17/1.28  tff(c_122, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_61, c_61, c_114])).
% 2.17/1.28  tff(c_10, plain, (![A_8, B_10]: (k7_subset_1(u1_struct_0(A_8), k2_pre_topc(A_8, B_10), k1_tops_1(A_8, B_10))=k2_tops_1(A_8, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.28  tff(c_130, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_122, c_10])).
% 2.17/1.28  tff(c_134, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_130])).
% 2.17/1.28  tff(c_87, plain, (![A_24, B_25]: (k7_subset_1(u1_struct_0(A_24), k2_pre_topc(A_24, B_25), k1_tops_1(A_24, B_25))=k2_tops_1(A_24, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.28  tff(c_102, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_87])).
% 2.17/1.28  tff(c_110, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_61, c_102])).
% 2.17/1.28  tff(c_138, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_110])).
% 2.17/1.28  tff(c_144, plain, (k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_138])).
% 2.17/1.28  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_144])).
% 2.17/1.28  tff(c_148, plain, (k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_14])).
% 2.17/1.28  tff(c_147, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_14])).
% 2.17/1.28  tff(c_157, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_147])).
% 2.17/1.28  tff(c_158, plain, (![B_26, A_27]: (v6_tops_1(B_26, A_27) | k1_tops_1(A_27, k2_pre_topc(A_27, B_26))!=B_26 | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.28  tff(c_162, plain, (v6_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_158])).
% 2.17/1.28  tff(c_167, plain, (v6_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_61, c_162])).
% 2.17/1.28  tff(c_168, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_167])).
% 2.17/1.28  tff(c_171, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_168])).
% 2.17/1.28  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_171])).
% 2.17/1.28  tff(c_177, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_167])).
% 2.17/1.28  tff(c_181, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_177, c_12])).
% 2.17/1.28  tff(c_189, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_61, c_61, c_181])).
% 2.17/1.28  tff(c_200, plain, (![A_28, B_29]: (k7_subset_1(u1_struct_0(A_28), k2_pre_topc(A_28, B_29), k1_tops_1(A_28, B_29))=k2_tops_1(A_28, B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.28  tff(c_209, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_189, c_200])).
% 2.17/1.28  tff(c_219, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_209])).
% 2.17/1.28  tff(c_221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_219])).
% 2.17/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.28  
% 2.17/1.28  Inference rules
% 2.17/1.28  ----------------------
% 2.17/1.28  #Ref     : 0
% 2.17/1.28  #Sup     : 46
% 2.17/1.28  #Fact    : 0
% 2.17/1.28  #Define  : 0
% 2.17/1.28  #Split   : 5
% 2.17/1.28  #Chain   : 0
% 2.17/1.28  #Close   : 0
% 2.17/1.28  
% 2.17/1.28  Ordering : KBO
% 2.17/1.28  
% 2.17/1.28  Simplification rules
% 2.17/1.28  ----------------------
% 2.17/1.28  #Subsume      : 0
% 2.17/1.28  #Demod        : 49
% 2.17/1.28  #Tautology    : 27
% 2.17/1.28  #SimpNegUnit  : 4
% 2.17/1.28  #BackRed      : 1
% 2.17/1.28  
% 2.17/1.28  #Partial instantiations: 0
% 2.17/1.28  #Strategies tried      : 1
% 2.17/1.28  
% 2.17/1.28  Timing (in seconds)
% 2.17/1.28  ----------------------
% 2.17/1.28  Preprocessing        : 0.27
% 2.17/1.28  Parsing              : 0.15
% 2.17/1.28  CNF conversion       : 0.02
% 2.17/1.28  Main loop            : 0.18
% 2.17/1.28  Inferencing          : 0.07
% 2.17/1.28  Reduction            : 0.06
% 2.17/1.28  Demodulation         : 0.04
% 2.17/1.28  BG Simplification    : 0.01
% 2.17/1.28  Subsumption          : 0.03
% 2.17/1.28  Abstraction          : 0.01
% 2.17/1.28  MUC search           : 0.00
% 2.17/1.28  Cooper               : 0.00
% 2.17/1.28  Total                : 0.48
% 2.17/1.28  Index Insertion      : 0.00
% 2.17/1.28  Index Deletion       : 0.00
% 2.17/1.28  Index Matching       : 0.00
% 2.17/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
