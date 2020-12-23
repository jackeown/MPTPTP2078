%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:29 EST 2020

% Result     : Theorem 4.67s
% Output     : CNFRefutation 4.93s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 273 expanded)
%              Number of leaves         :   34 ( 107 expanded)
%              Depth                    :   10
%              Number of atoms          :  158 ( 598 expanded)
%              Number of equality atoms :   63 ( 153 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(f_111,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2673,plain,(
    ! [A_170,B_171,C_172] :
      ( k7_subset_1(A_170,B_171,C_172) = k4_xboole_0(B_171,C_172)
      | ~ m1_subset_1(B_171,k1_zfmisc_1(A_170)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2679,plain,(
    ! [C_172] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_172) = k4_xboole_0('#skF_2',C_172) ),
    inference(resolution,[status(thm)],[c_32,c_2673])).

tff(c_38,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_117,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_840,plain,(
    ! [B_88,A_89] :
      ( v4_pre_topc(B_88,A_89)
      | k2_pre_topc(A_89,B_88) != B_88
      | ~ v2_pre_topc(A_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_850,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_840])).

tff(c_855,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_850])).

tff(c_856,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_855])).

tff(c_1026,plain,(
    ! [A_99,B_100] :
      ( k4_subset_1(u1_struct_0(A_99),B_100,k2_tops_1(A_99,B_100)) = k2_pre_topc(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1033,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1026])).

tff(c_1038,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1033])).

tff(c_228,plain,(
    ! [A_56,B_57,C_58] :
      ( k7_subset_1(A_56,B_57,C_58) = k4_xboole_0(B_57,C_58)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_235,plain,(
    ! [C_59] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_59) = k4_xboole_0('#skF_2',C_59) ),
    inference(resolution,[status(thm)],[c_32,c_228])).

tff(c_44,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_149,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_44])).

tff(c_241,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_149])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [A_40,B_41] : k2_xboole_0(k4_xboole_0(A_40,B_41),A_40) = A_40 ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_90,plain,(
    ! [A_40,B_41] : k2_xboole_0(A_40,k4_xboole_0(A_40,B_41)) = A_40 ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_2])).

tff(c_253,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_90])).

tff(c_421,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1(k2_tops_1(A_67,B_68),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k3_subset_1(A_9,k3_subset_1(A_9,B_10)) = B_10
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2454,plain,(
    ! [A_156,B_157] :
      ( k3_subset_1(u1_struct_0(A_156),k3_subset_1(u1_struct_0(A_156),k2_tops_1(A_156,B_157))) = k2_tops_1(A_156,B_157)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(resolution,[status(thm)],[c_421,c_10])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k3_subset_1(A_7,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2148,plain,(
    ! [A_148,B_149] :
      ( k4_xboole_0(u1_struct_0(A_148),k2_tops_1(A_148,B_149)) = k3_subset_1(u1_struct_0(A_148),k2_tops_1(A_148,B_149))
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(resolution,[status(thm)],[c_421,c_8])).

tff(c_2155,plain,
    ( k4_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2148])).

tff(c_2160,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2155])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_187,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = k3_subset_1(A_52,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_213,plain,(
    ! [B_54,A_55] :
      ( k4_xboole_0(B_54,A_55) = k3_subset_1(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(resolution,[status(thm)],[c_18,c_187])).

tff(c_383,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = k3_subset_1(A_65,k4_xboole_0(A_65,B_66)) ),
    inference(resolution,[status(thm)],[c_6,c_213])).

tff(c_398,plain,(
    ! [A_65,B_66] : r1_tarski(k3_subset_1(A_65,k4_xboole_0(A_65,B_66)),A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_6])).

tff(c_2222,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2160,c_398])).

tff(c_2469,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2454,c_2222])).

tff(c_2490,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2469])).

tff(c_599,plain,(
    ! [A_77,B_78,C_79] :
      ( k4_subset_1(A_77,B_78,C_79) = k2_xboole_0(B_78,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_77))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1374,plain,(
    ! [B_110,B_111,A_112] :
      ( k4_subset_1(B_110,B_111,A_112) = k2_xboole_0(B_111,A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(B_110))
      | ~ r1_tarski(A_112,B_110) ) ),
    inference(resolution,[status(thm)],[c_18,c_599])).

tff(c_1383,plain,(
    ! [A_112] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_112) = k2_xboole_0('#skF_2',A_112)
      | ~ r1_tarski(A_112,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_32,c_1374])).

tff(c_2504,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2490,c_1383])).

tff(c_2527,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_253,c_2504])).

tff(c_2529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_856,c_2527])).

tff(c_2530,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2680,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2679,c_2530])).

tff(c_2531,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2986,plain,(
    ! [A_196,B_197] :
      ( r1_tarski(k2_tops_1(A_196,B_197),B_197)
      | ~ v4_pre_topc(B_197,A_196)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2993,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2986])).

tff(c_2998,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2531,c_2993])).

tff(c_2597,plain,(
    ! [A_166,B_167] :
      ( k4_xboole_0(A_166,B_167) = k3_subset_1(A_166,B_167)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(A_166)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2604,plain,(
    ! [B_18,A_17] :
      ( k4_xboole_0(B_18,A_17) = k3_subset_1(B_18,A_17)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(resolution,[status(thm)],[c_18,c_2597])).

tff(c_3008,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2998,c_2604])).

tff(c_3494,plain,(
    ! [A_218,B_219] :
      ( k7_subset_1(u1_struct_0(A_218),B_219,k2_tops_1(A_218,B_219)) = k1_tops_1(A_218,B_219)
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3501,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_3494])).

tff(c_3506,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3008,c_2679,c_3501])).

tff(c_2553,plain,(
    ! [A_162,B_163] :
      ( k3_subset_1(A_162,k3_subset_1(A_162,B_163)) = B_163
      | ~ m1_subset_1(B_163,k1_zfmisc_1(A_162)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2558,plain,(
    ! [B_18,A_17] :
      ( k3_subset_1(B_18,k3_subset_1(B_18,A_17)) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(resolution,[status(thm)],[c_18,c_2553])).

tff(c_3520,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3506,c_2558])).

tff(c_3524,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2998,c_3520])).

tff(c_3516,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3506,c_3008])).

tff(c_2623,plain,(
    ! [B_168,A_169] :
      ( k4_xboole_0(B_168,A_169) = k3_subset_1(B_168,A_169)
      | ~ r1_tarski(A_169,B_168) ) ),
    inference(resolution,[status(thm)],[c_18,c_2597])).

tff(c_2637,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_subset_1(A_5,k4_xboole_0(A_5,B_6)) ),
    inference(resolution,[status(thm)],[c_6,c_2623])).

tff(c_3586,plain,(
    k3_subset_1('#skF_2',k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3516,c_2637])).

tff(c_3599,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3516,c_3586])).

tff(c_3701,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3524,c_3599])).

tff(c_3702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2680,c_3701])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.67/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.93/1.90  
% 4.93/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.93/1.90  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 4.93/1.90  
% 4.93/1.90  %Foreground sorts:
% 4.93/1.90  
% 4.93/1.90  
% 4.93/1.90  %Background operators:
% 4.93/1.90  
% 4.93/1.90  
% 4.93/1.90  %Foreground operators:
% 4.93/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.93/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.93/1.90  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.93/1.90  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.93/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.93/1.90  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.93/1.90  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.93/1.90  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.93/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.93/1.90  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.93/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.93/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.93/1.90  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.93/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.93/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.93/1.90  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.93/1.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.93/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.93/1.90  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.93/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.93/1.90  
% 4.93/1.92  tff(f_111, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 4.93/1.92  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.93/1.92  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.93/1.92  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 4.93/1.92  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.93/1.92  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.93/1.92  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.93/1.92  tff(f_76, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.93/1.92  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.93/1.92  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.93/1.92  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.93/1.92  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.93/1.92  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 4.93/1.92  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 4.93/1.92  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.93/1.92  tff(c_2673, plain, (![A_170, B_171, C_172]: (k7_subset_1(A_170, B_171, C_172)=k4_xboole_0(B_171, C_172) | ~m1_subset_1(B_171, k1_zfmisc_1(A_170)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.93/1.92  tff(c_2679, plain, (![C_172]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_172)=k4_xboole_0('#skF_2', C_172))), inference(resolution, [status(thm)], [c_32, c_2673])).
% 4.93/1.92  tff(c_38, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.93/1.92  tff(c_117, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 4.93/1.92  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.93/1.92  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.93/1.92  tff(c_840, plain, (![B_88, A_89]: (v4_pre_topc(B_88, A_89) | k2_pre_topc(A_89, B_88)!=B_88 | ~v2_pre_topc(A_89) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.93/1.92  tff(c_850, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_840])).
% 4.93/1.92  tff(c_855, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_850])).
% 4.93/1.92  tff(c_856, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_117, c_855])).
% 4.93/1.92  tff(c_1026, plain, (![A_99, B_100]: (k4_subset_1(u1_struct_0(A_99), B_100, k2_tops_1(A_99, B_100))=k2_pre_topc(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.93/1.92  tff(c_1033, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1026])).
% 4.93/1.92  tff(c_1038, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1033])).
% 4.93/1.92  tff(c_228, plain, (![A_56, B_57, C_58]: (k7_subset_1(A_56, B_57, C_58)=k4_xboole_0(B_57, C_58) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.93/1.92  tff(c_235, plain, (![C_59]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_59)=k4_xboole_0('#skF_2', C_59))), inference(resolution, [status(thm)], [c_32, c_228])).
% 4.93/1.92  tff(c_44, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.93/1.92  tff(c_149, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_117, c_44])).
% 4.93/1.92  tff(c_241, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_235, c_149])).
% 4.93/1.92  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.93/1.92  tff(c_79, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.93/1.92  tff(c_84, plain, (![A_40, B_41]: (k2_xboole_0(k4_xboole_0(A_40, B_41), A_40)=A_40)), inference(resolution, [status(thm)], [c_6, c_79])).
% 4.93/1.92  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.93/1.92  tff(c_90, plain, (![A_40, B_41]: (k2_xboole_0(A_40, k4_xboole_0(A_40, B_41))=A_40)), inference(superposition, [status(thm), theory('equality')], [c_84, c_2])).
% 4.93/1.92  tff(c_253, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_241, c_90])).
% 4.93/1.92  tff(c_421, plain, (![A_67, B_68]: (m1_subset_1(k2_tops_1(A_67, B_68), k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.93/1.92  tff(c_10, plain, (![A_9, B_10]: (k3_subset_1(A_9, k3_subset_1(A_9, B_10))=B_10 | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.93/1.92  tff(c_2454, plain, (![A_156, B_157]: (k3_subset_1(u1_struct_0(A_156), k3_subset_1(u1_struct_0(A_156), k2_tops_1(A_156, B_157)))=k2_tops_1(A_156, B_157) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(resolution, [status(thm)], [c_421, c_10])).
% 4.93/1.92  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k3_subset_1(A_7, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.93/1.92  tff(c_2148, plain, (![A_148, B_149]: (k4_xboole_0(u1_struct_0(A_148), k2_tops_1(A_148, B_149))=k3_subset_1(u1_struct_0(A_148), k2_tops_1(A_148, B_149)) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(resolution, [status(thm)], [c_421, c_8])).
% 4.93/1.92  tff(c_2155, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2148])).
% 4.93/1.92  tff(c_2160, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2155])).
% 4.93/1.92  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.93/1.92  tff(c_187, plain, (![A_52, B_53]: (k4_xboole_0(A_52, B_53)=k3_subset_1(A_52, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.93/1.92  tff(c_213, plain, (![B_54, A_55]: (k4_xboole_0(B_54, A_55)=k3_subset_1(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(resolution, [status(thm)], [c_18, c_187])).
% 4.93/1.92  tff(c_383, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(A_65, B_66))=k3_subset_1(A_65, k4_xboole_0(A_65, B_66)))), inference(resolution, [status(thm)], [c_6, c_213])).
% 4.93/1.92  tff(c_398, plain, (![A_65, B_66]: (r1_tarski(k3_subset_1(A_65, k4_xboole_0(A_65, B_66)), A_65))), inference(superposition, [status(thm), theory('equality')], [c_383, c_6])).
% 4.93/1.92  tff(c_2222, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2160, c_398])).
% 4.93/1.92  tff(c_2469, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2454, c_2222])).
% 4.93/1.92  tff(c_2490, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_2469])).
% 4.93/1.92  tff(c_599, plain, (![A_77, B_78, C_79]: (k4_subset_1(A_77, B_78, C_79)=k2_xboole_0(B_78, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(A_77)) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.93/1.92  tff(c_1374, plain, (![B_110, B_111, A_112]: (k4_subset_1(B_110, B_111, A_112)=k2_xboole_0(B_111, A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(B_110)) | ~r1_tarski(A_112, B_110))), inference(resolution, [status(thm)], [c_18, c_599])).
% 4.93/1.92  tff(c_1383, plain, (![A_112]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_112)=k2_xboole_0('#skF_2', A_112) | ~r1_tarski(A_112, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_32, c_1374])).
% 4.93/1.92  tff(c_2504, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2490, c_1383])).
% 4.93/1.92  tff(c_2527, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1038, c_253, c_2504])).
% 4.93/1.92  tff(c_2529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_856, c_2527])).
% 4.93/1.92  tff(c_2530, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 4.93/1.92  tff(c_2680, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2679, c_2530])).
% 4.93/1.92  tff(c_2531, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_38])).
% 4.93/1.92  tff(c_2986, plain, (![A_196, B_197]: (r1_tarski(k2_tops_1(A_196, B_197), B_197) | ~v4_pre_topc(B_197, A_196) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_196))) | ~l1_pre_topc(A_196))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.93/1.92  tff(c_2993, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2986])).
% 4.93/1.92  tff(c_2998, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2531, c_2993])).
% 4.93/1.92  tff(c_2597, plain, (![A_166, B_167]: (k4_xboole_0(A_166, B_167)=k3_subset_1(A_166, B_167) | ~m1_subset_1(B_167, k1_zfmisc_1(A_166)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.93/1.92  tff(c_2604, plain, (![B_18, A_17]: (k4_xboole_0(B_18, A_17)=k3_subset_1(B_18, A_17) | ~r1_tarski(A_17, B_18))), inference(resolution, [status(thm)], [c_18, c_2597])).
% 4.93/1.92  tff(c_3008, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2998, c_2604])).
% 4.93/1.92  tff(c_3494, plain, (![A_218, B_219]: (k7_subset_1(u1_struct_0(A_218), B_219, k2_tops_1(A_218, B_219))=k1_tops_1(A_218, B_219) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.93/1.92  tff(c_3501, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_3494])).
% 4.93/1.92  tff(c_3506, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3008, c_2679, c_3501])).
% 4.93/1.92  tff(c_2553, plain, (![A_162, B_163]: (k3_subset_1(A_162, k3_subset_1(A_162, B_163))=B_163 | ~m1_subset_1(B_163, k1_zfmisc_1(A_162)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.93/1.92  tff(c_2558, plain, (![B_18, A_17]: (k3_subset_1(B_18, k3_subset_1(B_18, A_17))=A_17 | ~r1_tarski(A_17, B_18))), inference(resolution, [status(thm)], [c_18, c_2553])).
% 4.93/1.92  tff(c_3520, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3506, c_2558])).
% 4.93/1.92  tff(c_3524, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2998, c_3520])).
% 4.93/1.92  tff(c_3516, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3506, c_3008])).
% 4.93/1.92  tff(c_2623, plain, (![B_168, A_169]: (k4_xboole_0(B_168, A_169)=k3_subset_1(B_168, A_169) | ~r1_tarski(A_169, B_168))), inference(resolution, [status(thm)], [c_18, c_2597])).
% 4.93/1.92  tff(c_2637, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_subset_1(A_5, k4_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_6, c_2623])).
% 4.93/1.92  tff(c_3586, plain, (k3_subset_1('#skF_2', k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3516, c_2637])).
% 4.93/1.92  tff(c_3599, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3516, c_3586])).
% 4.93/1.92  tff(c_3701, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3524, c_3599])).
% 4.93/1.92  tff(c_3702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2680, c_3701])).
% 4.93/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.93/1.92  
% 4.93/1.92  Inference rules
% 4.93/1.92  ----------------------
% 4.93/1.92  #Ref     : 0
% 4.93/1.92  #Sup     : 906
% 4.93/1.92  #Fact    : 0
% 4.93/1.92  #Define  : 0
% 4.93/1.92  #Split   : 1
% 4.93/1.92  #Chain   : 0
% 4.93/1.92  #Close   : 0
% 4.93/1.92  
% 4.93/1.92  Ordering : KBO
% 4.93/1.92  
% 4.93/1.92  Simplification rules
% 4.93/1.92  ----------------------
% 4.93/1.92  #Subsume      : 14
% 4.93/1.92  #Demod        : 780
% 4.93/1.92  #Tautology    : 547
% 4.93/1.92  #SimpNegUnit  : 6
% 4.93/1.92  #BackRed      : 24
% 4.93/1.92  
% 4.93/1.92  #Partial instantiations: 0
% 4.93/1.92  #Strategies tried      : 1
% 4.93/1.92  
% 4.93/1.92  Timing (in seconds)
% 4.93/1.92  ----------------------
% 4.93/1.92  Preprocessing        : 0.32
% 4.93/1.92  Parsing              : 0.18
% 4.93/1.92  CNF conversion       : 0.02
% 4.93/1.92  Main loop            : 0.82
% 4.93/1.92  Inferencing          : 0.27
% 4.93/1.92  Reduction            : 0.32
% 4.93/1.92  Demodulation         : 0.25
% 4.93/1.92  BG Simplification    : 0.03
% 4.93/1.92  Subsumption          : 0.13
% 4.93/1.92  Abstraction          : 0.05
% 4.93/1.92  MUC search           : 0.00
% 4.93/1.92  Cooper               : 0.00
% 4.93/1.92  Total                : 1.17
% 4.93/1.92  Index Insertion      : 0.00
% 4.93/1.92  Index Deletion       : 0.00
% 4.93/1.92  Index Matching       : 0.00
% 4.93/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
