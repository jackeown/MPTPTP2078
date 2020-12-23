%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:34 EST 2020

% Result     : Theorem 8.04s
% Output     : CNFRefutation 8.16s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 138 expanded)
%              Number of leaves         :   34 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  130 ( 272 expanded)
%              Number of equality atoms :   53 (  87 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_68,axiom,(
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

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_14189,plain,(
    ! [A_236,B_237,C_238] :
      ( k7_subset_1(A_236,B_237,C_238) = k4_xboole_0(B_237,C_238)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(A_236)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14192,plain,(
    ! [C_238] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_238) = k4_xboole_0('#skF_2',C_238) ),
    inference(resolution,[status(thm)],[c_32,c_14189])).

tff(c_38,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_80,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1490,plain,(
    ! [B_92,A_93] :
      ( v4_pre_topc(B_92,A_93)
      | k2_pre_topc(A_93,B_92) != B_92
      | ~ v2_pre_topc(A_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1496,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1490])).

tff(c_1500,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_1496])).

tff(c_1501,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1500])).

tff(c_2309,plain,(
    ! [A_108,B_109] :
      ( k4_subset_1(u1_struct_0(A_108),B_109,k2_tops_1(A_108,B_109)) = k2_pre_topc(A_108,B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2313,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2309])).

tff(c_2317,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2313])).

tff(c_288,plain,(
    ! [A_55,B_56,C_57] :
      ( k7_subset_1(A_55,B_56,C_57) = k4_xboole_0(B_56,C_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_292,plain,(
    ! [C_58] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_58) = k4_xboole_0('#skF_2',C_58) ),
    inference(resolution,[status(thm)],[c_32,c_288])).

tff(c_44,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_223,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_44])).

tff(c_298,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_223])).

tff(c_8,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(B_37,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ r1_tarski(A_39,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_67])).

tff(c_99,plain,(
    ! [B_40] : k4_xboole_0(k1_xboole_0,B_40) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_81])).

tff(c_16,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_104,plain,(
    ! [B_40] : k5_xboole_0(B_40,k1_xboole_0) = k2_xboole_0(B_40,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_16])).

tff(c_111,plain,(
    ! [B_40] : k5_xboole_0(B_40,k1_xboole_0) = B_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_104])).

tff(c_135,plain,(
    ! [A_44,B_45,C_46] :
      ( r1_tarski(k4_xboole_0(A_44,B_45),C_46)
      | ~ r1_tarski(A_44,k2_xboole_0(B_45,C_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_79,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_67])).

tff(c_143,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = k1_xboole_0
      | ~ r1_tarski(A_44,k2_xboole_0(B_45,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_135,c_79])).

tff(c_155,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = k1_xboole_0
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_143])).

tff(c_228,plain,(
    ! [A_51,B_52] : k4_xboole_0(k4_xboole_0(A_51,B_52),A_51) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_155])).

tff(c_242,plain,(
    ! [A_51,B_52] : k2_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k5_xboole_0(A_51,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_16])).

tff(c_261,plain,(
    ! [A_51,B_52] : k2_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_242])).

tff(c_310,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_261])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k2_tops_1(A_21,B_22),k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1019,plain,(
    ! [A_81,B_82,C_83] :
      ( k4_subset_1(A_81,B_82,C_83) = k2_xboole_0(B_82,C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_13447,plain,(
    ! [A_214,B_215,B_216] :
      ( k4_subset_1(u1_struct_0(A_214),B_215,k2_tops_1(A_214,B_216)) = k2_xboole_0(B_215,k2_tops_1(A_214,B_216))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214) ) ),
    inference(resolution,[status(thm)],[c_26,c_1019])).

tff(c_13451,plain,(
    ! [B_216] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_216)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_216))
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_13447])).

tff(c_13969,plain,(
    ! [B_219] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_219)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_219))
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_13451])).

tff(c_13976,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_13969])).

tff(c_13981,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2317,c_310,c_13976])).

tff(c_13983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1501,c_13981])).

tff(c_13984,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_14193,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14192,c_13984])).

tff(c_13985,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_14281,plain,(
    ! [A_247,B_248] :
      ( k2_pre_topc(A_247,B_248) = B_248
      | ~ v4_pre_topc(B_248,A_247)
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ l1_pre_topc(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14287,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_14281])).

tff(c_14291,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_13985,c_14287])).

tff(c_18989,plain,(
    ! [A_331,B_332] :
      ( k7_subset_1(u1_struct_0(A_331),k2_pre_topc(A_331,B_332),k1_tops_1(A_331,B_332)) = k2_tops_1(A_331,B_332)
      | ~ m1_subset_1(B_332,k1_zfmisc_1(u1_struct_0(A_331)))
      | ~ l1_pre_topc(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18998,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14291,c_18989])).

tff(c_19002,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_14192,c_18998])).

tff(c_19004,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14193,c_19002])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:35:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.04/3.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.14/3.07  
% 8.14/3.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.16/3.07  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.16/3.07  
% 8.16/3.07  %Foreground sorts:
% 8.16/3.07  
% 8.16/3.07  
% 8.16/3.07  %Background operators:
% 8.16/3.07  
% 8.16/3.07  
% 8.16/3.07  %Foreground operators:
% 8.16/3.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.16/3.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.16/3.07  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.16/3.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.16/3.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.16/3.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.16/3.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.16/3.07  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.16/3.07  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.16/3.07  tff('#skF_2', type, '#skF_2': $i).
% 8.16/3.07  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.16/3.07  tff('#skF_1', type, '#skF_1': $i).
% 8.16/3.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.16/3.07  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.16/3.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.16/3.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.16/3.07  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.16/3.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.16/3.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.16/3.07  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.16/3.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.16/3.07  
% 8.16/3.09  tff(f_100, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 8.16/3.09  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.16/3.09  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 8.16/3.09  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 8.16/3.09  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.16/3.09  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.16/3.09  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.16/3.09  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.16/3.09  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.16/3.09  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 8.16/3.09  tff(f_74, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 8.16/3.09  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.16/3.09  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 8.16/3.09  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.16/3.09  tff(c_14189, plain, (![A_236, B_237, C_238]: (k7_subset_1(A_236, B_237, C_238)=k4_xboole_0(B_237, C_238) | ~m1_subset_1(B_237, k1_zfmisc_1(A_236)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.16/3.09  tff(c_14192, plain, (![C_238]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_238)=k4_xboole_0('#skF_2', C_238))), inference(resolution, [status(thm)], [c_32, c_14189])).
% 8.16/3.09  tff(c_38, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.16/3.09  tff(c_80, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 8.16/3.09  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.16/3.09  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.16/3.09  tff(c_1490, plain, (![B_92, A_93]: (v4_pre_topc(B_92, A_93) | k2_pre_topc(A_93, B_92)!=B_92 | ~v2_pre_topc(A_93) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.16/3.09  tff(c_1496, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1490])).
% 8.16/3.09  tff(c_1500, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_1496])).
% 8.16/3.09  tff(c_1501, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_80, c_1500])).
% 8.16/3.09  tff(c_2309, plain, (![A_108, B_109]: (k4_subset_1(u1_struct_0(A_108), B_109, k2_tops_1(A_108, B_109))=k2_pre_topc(A_108, B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.16/3.09  tff(c_2313, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2309])).
% 8.16/3.09  tff(c_2317, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2313])).
% 8.16/3.09  tff(c_288, plain, (![A_55, B_56, C_57]: (k7_subset_1(A_55, B_56, C_57)=k4_xboole_0(B_56, C_57) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.16/3.09  tff(c_292, plain, (![C_58]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_58)=k4_xboole_0('#skF_2', C_58))), inference(resolution, [status(thm)], [c_32, c_288])).
% 8.16/3.09  tff(c_44, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.16/3.09  tff(c_223, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_80, c_44])).
% 8.16/3.09  tff(c_298, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_292, c_223])).
% 8.16/3.09  tff(c_8, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.16/3.09  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.16/3.09  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.16/3.09  tff(c_67, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(B_37, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.16/3.09  tff(c_81, plain, (![A_39]: (k1_xboole_0=A_39 | ~r1_tarski(A_39, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_67])).
% 8.16/3.09  tff(c_99, plain, (![B_40]: (k4_xboole_0(k1_xboole_0, B_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_81])).
% 8.16/3.09  tff(c_16, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.16/3.09  tff(c_104, plain, (![B_40]: (k5_xboole_0(B_40, k1_xboole_0)=k2_xboole_0(B_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_99, c_16])).
% 8.16/3.09  tff(c_111, plain, (![B_40]: (k5_xboole_0(B_40, k1_xboole_0)=B_40)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_104])).
% 8.16/3.09  tff(c_135, plain, (![A_44, B_45, C_46]: (r1_tarski(k4_xboole_0(A_44, B_45), C_46) | ~r1_tarski(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.16/3.09  tff(c_79, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_67])).
% 8.16/3.09  tff(c_143, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=k1_xboole_0 | ~r1_tarski(A_44, k2_xboole_0(B_45, k1_xboole_0)))), inference(resolution, [status(thm)], [c_135, c_79])).
% 8.16/3.09  tff(c_155, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=k1_xboole_0 | ~r1_tarski(A_47, B_48))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_143])).
% 8.16/3.09  tff(c_228, plain, (![A_51, B_52]: (k4_xboole_0(k4_xboole_0(A_51, B_52), A_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_155])).
% 8.16/3.09  tff(c_242, plain, (![A_51, B_52]: (k2_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k5_xboole_0(A_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_228, c_16])).
% 8.16/3.09  tff(c_261, plain, (![A_51, B_52]: (k2_xboole_0(A_51, k4_xboole_0(A_51, B_52))=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_242])).
% 8.16/3.09  tff(c_310, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_298, c_261])).
% 8.16/3.09  tff(c_26, plain, (![A_21, B_22]: (m1_subset_1(k2_tops_1(A_21, B_22), k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.16/3.09  tff(c_1019, plain, (![A_81, B_82, C_83]: (k4_subset_1(A_81, B_82, C_83)=k2_xboole_0(B_82, C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.16/3.09  tff(c_13447, plain, (![A_214, B_215, B_216]: (k4_subset_1(u1_struct_0(A_214), B_215, k2_tops_1(A_214, B_216))=k2_xboole_0(B_215, k2_tops_1(A_214, B_216)) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0(A_214))) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_214))) | ~l1_pre_topc(A_214))), inference(resolution, [status(thm)], [c_26, c_1019])).
% 8.16/3.09  tff(c_13451, plain, (![B_216]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_216))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_216)) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_13447])).
% 8.16/3.09  tff(c_13969, plain, (![B_219]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_219))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_219)) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_13451])).
% 8.16/3.09  tff(c_13976, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_13969])).
% 8.16/3.09  tff(c_13981, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2317, c_310, c_13976])).
% 8.16/3.09  tff(c_13983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1501, c_13981])).
% 8.16/3.09  tff(c_13984, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 8.16/3.09  tff(c_14193, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14192, c_13984])).
% 8.16/3.09  tff(c_13985, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_38])).
% 8.16/3.09  tff(c_14281, plain, (![A_247, B_248]: (k2_pre_topc(A_247, B_248)=B_248 | ~v4_pre_topc(B_248, A_247) | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0(A_247))) | ~l1_pre_topc(A_247))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.16/3.09  tff(c_14287, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_14281])).
% 8.16/3.09  tff(c_14291, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_13985, c_14287])).
% 8.16/3.09  tff(c_18989, plain, (![A_331, B_332]: (k7_subset_1(u1_struct_0(A_331), k2_pre_topc(A_331, B_332), k1_tops_1(A_331, B_332))=k2_tops_1(A_331, B_332) | ~m1_subset_1(B_332, k1_zfmisc_1(u1_struct_0(A_331))) | ~l1_pre_topc(A_331))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.16/3.09  tff(c_18998, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14291, c_18989])).
% 8.16/3.09  tff(c_19002, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_14192, c_18998])).
% 8.16/3.09  tff(c_19004, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14193, c_19002])).
% 8.16/3.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.16/3.09  
% 8.16/3.09  Inference rules
% 8.16/3.09  ----------------------
% 8.16/3.09  #Ref     : 0
% 8.16/3.09  #Sup     : 4303
% 8.16/3.09  #Fact    : 0
% 8.16/3.09  #Define  : 0
% 8.16/3.09  #Split   : 4
% 8.16/3.09  #Chain   : 0
% 8.16/3.09  #Close   : 0
% 8.16/3.09  
% 8.16/3.09  Ordering : KBO
% 8.16/3.09  
% 8.16/3.09  Simplification rules
% 8.16/3.09  ----------------------
% 8.16/3.09  #Subsume      : 694
% 8.16/3.09  #Demod        : 5486
% 8.16/3.09  #Tautology    : 3176
% 8.16/3.09  #SimpNegUnit  : 4
% 8.16/3.09  #BackRed      : 1
% 8.16/3.09  
% 8.16/3.09  #Partial instantiations: 0
% 8.16/3.09  #Strategies tried      : 1
% 8.16/3.09  
% 8.16/3.09  Timing (in seconds)
% 8.16/3.09  ----------------------
% 8.16/3.09  Preprocessing        : 0.34
% 8.16/3.09  Parsing              : 0.18
% 8.16/3.09  CNF conversion       : 0.02
% 8.16/3.09  Main loop            : 1.94
% 8.16/3.09  Inferencing          : 0.58
% 8.16/3.09  Reduction            : 0.83
% 8.16/3.09  Demodulation         : 0.67
% 8.16/3.09  BG Simplification    : 0.06
% 8.16/3.09  Subsumption          : 0.38
% 8.16/3.09  Abstraction          : 0.10
% 8.16/3.09  MUC search           : 0.00
% 8.16/3.09  Cooper               : 0.00
% 8.16/3.09  Total                : 2.32
% 8.16/3.09  Index Insertion      : 0.00
% 8.16/3.09  Index Deletion       : 0.00
% 8.16/3.09  Index Matching       : 0.00
% 8.16/3.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
