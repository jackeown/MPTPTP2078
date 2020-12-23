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
% DateTime   : Thu Dec  3 10:21:44 EST 2020

% Result     : Theorem 15.70s
% Output     : CNFRefutation 15.86s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 514 expanded)
%              Number of leaves         :   31 ( 188 expanded)
%              Depth                    :   12
%              Number of atoms          :  248 (1077 expanded)
%              Number of equality atoms :   78 ( 311 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

tff(c_46,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_77,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_40,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_106,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_40])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    ! [A_27] :
      ( u1_struct_0(A_27) = k2_struct_0(A_27)
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_67,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(resolution,[status(thm)],[c_24,c_50])).

tff(c_71,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_67])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_72,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_36])).

tff(c_155,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(k3_subset_1(A_44,B_45),k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_342,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(k3_subset_1(A_61,B_62),A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(resolution,[status(thm)],[c_155,c_16])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_481,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(k3_subset_1(A_72,B_73),A_72) = k1_xboole_0
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(resolution,[status(thm)],[c_342,c_10])).

tff(c_499,plain,(
    k4_xboole_0(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_481])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_414,plain,(
    ! [A_66,B_67] :
      ( k2_pre_topc(A_66,B_67) = k2_struct_0(A_66)
      | ~ v1_tops_1(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_432,plain,(
    ! [B_67] :
      ( k2_pre_topc('#skF_1',B_67) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_67,'#skF_1')
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_414])).

tff(c_797,plain,(
    ! [B_89] :
      ( k2_pre_topc('#skF_1',B_89) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_89,'#skF_1')
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_432])).

tff(c_975,plain,(
    ! [A_96] :
      ( k2_pre_topc('#skF_1',A_96) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(A_96,'#skF_1')
      | ~ r1_tarski(A_96,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_797])).

tff(c_1802,plain,(
    ! [A_121] :
      ( k2_pre_topc('#skF_1',A_121) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(A_121,'#skF_1')
      | k4_xboole_0(A_121,k2_struct_0('#skF_1')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_975])).

tff(c_1852,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_1802])).

tff(c_2012,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1852])).

tff(c_269,plain,(
    ! [B_56,A_57] :
      ( v1_tops_1(B_56,A_57)
      | k2_pre_topc(A_57,B_56) != k2_struct_0(A_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_287,plain,(
    ! [B_56] :
      ( v1_tops_1(B_56,'#skF_1')
      | k2_pre_topc('#skF_1',B_56) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_269])).

tff(c_722,plain,(
    ! [B_84] :
      ( v1_tops_1(B_84,'#skF_1')
      | k2_pre_topc('#skF_1',B_84) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_287])).

tff(c_896,plain,(
    ! [A_93] :
      ( v1_tops_1(A_93,'#skF_1')
      | k2_pre_topc('#skF_1',A_93) != k2_struct_0('#skF_1')
      | ~ r1_tarski(A_93,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_722])).

tff(c_1705,plain,(
    ! [A_117] :
      ( v1_tops_1(A_117,'#skF_1')
      | k2_pre_topc('#skF_1',A_117) != k2_struct_0('#skF_1')
      | k4_xboole_0(A_117,k2_struct_0('#skF_1')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_896])).

tff(c_1751,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_1705])).

tff(c_2019,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2012,c_1751])).

tff(c_927,plain,(
    ! [A_94,B_95] :
      ( k3_subset_1(u1_struct_0(A_94),k2_pre_topc(A_94,k3_subset_1(u1_struct_0(A_94),B_95))) = k1_tops_1(A_94,B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_964,plain,(
    ! [B_95] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_95))) = k1_tops_1('#skF_1',B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_927])).

tff(c_971,plain,(
    ! [B_95] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_95))) = k1_tops_1('#skF_1',B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_71,c_71,c_964])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k3_subset_1(A_7,B_8),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_189,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k2_pre_topc(A_49,B_50),k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k3_subset_1(A_5,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1974,plain,(
    ! [A_131,B_132] :
      ( k4_xboole_0(u1_struct_0(A_131),k2_pre_topc(A_131,B_132)) = k3_subset_1(u1_struct_0(A_131),k2_pre_topc(A_131,B_132))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(resolution,[status(thm)],[c_189,c_12])).

tff(c_7273,plain,(
    ! [A_295,B_296] :
      ( k4_xboole_0(u1_struct_0(A_295),k2_pre_topc(A_295,k3_subset_1(u1_struct_0(A_295),B_296))) = k3_subset_1(u1_struct_0(A_295),k2_pre_topc(A_295,k3_subset_1(u1_struct_0(A_295),B_296)))
      | ~ l1_pre_topc(A_295)
      | ~ m1_subset_1(B_296,k1_zfmisc_1(u1_struct_0(A_295))) ) ),
    inference(resolution,[status(thm)],[c_14,c_1974])).

tff(c_1061,plain,(
    ! [A_99,B_100] :
      ( r1_tarski(k2_pre_topc(A_99,B_100),u1_struct_0(A_99))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_189,c_16])).

tff(c_107,plain,(
    ! [B_38,A_39] :
      ( B_38 = A_39
      | ~ r1_tarski(B_38,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_107])).

tff(c_1077,plain,(
    ! [A_99,B_100] :
      ( k2_pre_topc(A_99,B_100) = u1_struct_0(A_99)
      | k4_xboole_0(u1_struct_0(A_99),k2_pre_topc(A_99,B_100)) != k1_xboole_0
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_1061,c_115])).

tff(c_25971,plain,(
    ! [A_628,B_629] :
      ( k2_pre_topc(A_628,k3_subset_1(u1_struct_0(A_628),B_629)) = u1_struct_0(A_628)
      | k3_subset_1(u1_struct_0(A_628),k2_pre_topc(A_628,k3_subset_1(u1_struct_0(A_628),B_629))) != k1_xboole_0
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_628),B_629),k1_zfmisc_1(u1_struct_0(A_628)))
      | ~ l1_pre_topc(A_628)
      | ~ l1_pre_topc(A_628)
      | ~ m1_subset_1(B_629,k1_zfmisc_1(u1_struct_0(A_628))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7273,c_1077])).

tff(c_26014,plain,(
    ! [B_629] :
      ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_629)) = u1_struct_0('#skF_1')
      | k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_629))) != k1_xboole_0
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),B_629),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_629,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_25971])).

tff(c_26048,plain,(
    ! [B_630] :
      ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_630)) = k2_struct_0('#skF_1')
      | k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_630))) != k1_xboole_0
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),B_630),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_630,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_38,c_38,c_71,c_71,c_71,c_71,c_71,c_26014])).

tff(c_30565,plain,(
    ! [B_677] :
      ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_677)) = k2_struct_0('#skF_1')
      | k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_677))) != k1_xboole_0
      | ~ m1_subset_1(B_677,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_14,c_26048])).

tff(c_30677,plain,(
    ! [B_678] :
      ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_678)) = k2_struct_0('#skF_1')
      | k1_tops_1('#skF_1',B_678) != k1_xboole_0
      | ~ m1_subset_1(B_678,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_678,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_971,c_30565])).

tff(c_30704,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_72,c_30677])).

tff(c_30739,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_77,c_30704])).

tff(c_30741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2019,c_30739])).

tff(c_30743,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_1852])).

tff(c_671,plain,(
    ! [B_79,A_80] :
      ( v2_tops_1(B_79,A_80)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_80),B_79),A_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_678,plain,(
    ! [B_79] :
      ( v2_tops_1(B_79,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_79),'#skF_1')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_671])).

tff(c_680,plain,(
    ! [B_79] :
      ( v2_tops_1(B_79,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_79),'#skF_1')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_71,c_678])).

tff(c_30766,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_30743,c_680])).

tff(c_30769,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_30766])).

tff(c_30771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_30769])).

tff(c_30773,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_55])).

tff(c_30850,plain,(
    ! [A_695,B_696] :
      ( k4_xboole_0(A_695,B_696) = k3_subset_1(A_695,B_696)
      | ~ m1_subset_1(B_696,k1_zfmisc_1(A_695)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30882,plain,(
    ! [B_699,A_700] :
      ( k4_xboole_0(B_699,A_700) = k3_subset_1(B_699,A_700)
      | ~ r1_tarski(A_700,B_699) ) ),
    inference(resolution,[status(thm)],[c_18,c_30850])).

tff(c_30894,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k3_subset_1(B_2,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_30882])).

tff(c_30900,plain,(
    ! [B_2] : k3_subset_1(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_30894])).

tff(c_30772,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_31453,plain,(
    ! [A_736,B_737] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_736),B_737),A_736)
      | ~ v2_tops_1(B_737,A_736)
      | ~ m1_subset_1(B_737,k1_zfmisc_1(u1_struct_0(A_736)))
      | ~ l1_pre_topc(A_736) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_31463,plain,(
    ! [B_737] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_737),'#skF_1')
      | ~ v2_tops_1(B_737,'#skF_1')
      | ~ m1_subset_1(B_737,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_31453])).

tff(c_31466,plain,(
    ! [B_737] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_737),'#skF_1')
      | ~ v2_tops_1(B_737,'#skF_1')
      | ~ m1_subset_1(B_737,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_71,c_31463])).

tff(c_30833,plain,(
    ! [A_691,B_692] :
      ( m1_subset_1(k3_subset_1(A_691,B_692),k1_zfmisc_1(A_691))
      | ~ m1_subset_1(B_692,k1_zfmisc_1(A_691)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30838,plain,(
    ! [A_693,B_694] :
      ( r1_tarski(k3_subset_1(A_693,B_694),A_693)
      | ~ m1_subset_1(B_694,k1_zfmisc_1(A_693)) ) ),
    inference(resolution,[status(thm)],[c_30833,c_16])).

tff(c_31236,plain,(
    ! [A_724,B_725] :
      ( k4_xboole_0(k3_subset_1(A_724,B_725),A_724) = k1_xboole_0
      | ~ m1_subset_1(B_725,k1_zfmisc_1(A_724)) ) ),
    inference(resolution,[status(thm)],[c_30838,c_10])).

tff(c_31254,plain,(
    k4_xboole_0(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_31236])).

tff(c_31094,plain,(
    ! [A_714,B_715] :
      ( k2_pre_topc(A_714,B_715) = k2_struct_0(A_714)
      | ~ v1_tops_1(B_715,A_714)
      | ~ m1_subset_1(B_715,k1_zfmisc_1(u1_struct_0(A_714)))
      | ~ l1_pre_topc(A_714) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_31112,plain,(
    ! [B_715] :
      ( k2_pre_topc('#skF_1',B_715) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_715,'#skF_1')
      | ~ m1_subset_1(B_715,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_31094])).

tff(c_31166,plain,(
    ! [B_719] :
      ( k2_pre_topc('#skF_1',B_719) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_719,'#skF_1')
      | ~ m1_subset_1(B_719,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_31112])).

tff(c_31732,plain,(
    ! [A_750] :
      ( k2_pre_topc('#skF_1',A_750) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(A_750,'#skF_1')
      | ~ r1_tarski(A_750,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_31166])).

tff(c_32466,plain,(
    ! [A_771] :
      ( k2_pre_topc('#skF_1',A_771) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(A_771,'#skF_1')
      | k4_xboole_0(A_771,k2_struct_0('#skF_1')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_31732])).

tff(c_32511,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_31254,c_32466])).

tff(c_32638,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32511])).

tff(c_32641,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_31466,c_32638])).

tff(c_32645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_30772,c_32641])).

tff(c_32646,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_32511])).

tff(c_31580,plain,(
    ! [A_742,B_743] :
      ( k3_subset_1(u1_struct_0(A_742),k2_pre_topc(A_742,k3_subset_1(u1_struct_0(A_742),B_743))) = k1_tops_1(A_742,B_743)
      | ~ m1_subset_1(B_743,k1_zfmisc_1(u1_struct_0(A_742)))
      | ~ l1_pre_topc(A_742) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_31617,plain,(
    ! [B_743] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_743))) = k1_tops_1('#skF_1',B_743)
      | ~ m1_subset_1(B_743,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_31580])).

tff(c_32867,plain,(
    ! [B_790] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_790))) = k1_tops_1('#skF_1',B_790)
      | ~ m1_subset_1(B_790,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_71,c_71,c_31617])).

tff(c_32911,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_32646,c_32867])).

tff(c_32919,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_30900,c_32911])).

tff(c_32921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30773,c_32919])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:33:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.70/7.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.70/7.91  
% 15.70/7.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.70/7.91  %$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 15.70/7.91  
% 15.70/7.91  %Foreground sorts:
% 15.70/7.91  
% 15.70/7.91  
% 15.70/7.91  %Background operators:
% 15.70/7.91  
% 15.70/7.91  
% 15.70/7.91  %Foreground operators:
% 15.70/7.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.70/7.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.70/7.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.70/7.91  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 15.70/7.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 15.70/7.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.70/7.91  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 15.70/7.91  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 15.70/7.91  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 15.70/7.91  tff('#skF_2', type, '#skF_2': $i).
% 15.70/7.91  tff('#skF_1', type, '#skF_1': $i).
% 15.70/7.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.70/7.91  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 15.70/7.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.70/7.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.70/7.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.70/7.91  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 15.70/7.91  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 15.70/7.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.70/7.91  
% 15.86/7.93  tff(f_96, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 15.86/7.93  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 15.86/7.93  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 15.86/7.93  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 15.86/7.93  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 15.86/7.93  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 15.86/7.93  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 15.86/7.93  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 15.86/7.93  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 15.86/7.93  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 15.86/7.93  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.86/7.93  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 15.86/7.93  tff(c_46, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.86/7.93  tff(c_77, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 15.86/7.93  tff(c_40, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.86/7.93  tff(c_106, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_40])).
% 15.86/7.93  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.86/7.93  tff(c_24, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.86/7.93  tff(c_50, plain, (![A_27]: (u1_struct_0(A_27)=k2_struct_0(A_27) | ~l1_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.86/7.93  tff(c_67, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_pre_topc(A_31))), inference(resolution, [status(thm)], [c_24, c_50])).
% 15.86/7.93  tff(c_71, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_67])).
% 15.86/7.93  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.86/7.93  tff(c_72, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_36])).
% 15.86/7.93  tff(c_155, plain, (![A_44, B_45]: (m1_subset_1(k3_subset_1(A_44, B_45), k1_zfmisc_1(A_44)) | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.86/7.93  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.86/7.93  tff(c_342, plain, (![A_61, B_62]: (r1_tarski(k3_subset_1(A_61, B_62), A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(resolution, [status(thm)], [c_155, c_16])).
% 15.86/7.93  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.86/7.93  tff(c_481, plain, (![A_72, B_73]: (k4_xboole_0(k3_subset_1(A_72, B_73), A_72)=k1_xboole_0 | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(resolution, [status(thm)], [c_342, c_10])).
% 15.86/7.93  tff(c_499, plain, (k4_xboole_0(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_481])).
% 15.86/7.93  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.86/7.93  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.86/7.93  tff(c_414, plain, (![A_66, B_67]: (k2_pre_topc(A_66, B_67)=k2_struct_0(A_66) | ~v1_tops_1(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_77])).
% 15.86/7.93  tff(c_432, plain, (![B_67]: (k2_pre_topc('#skF_1', B_67)=k2_struct_0('#skF_1') | ~v1_tops_1(B_67, '#skF_1') | ~m1_subset_1(B_67, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_414])).
% 15.86/7.93  tff(c_797, plain, (![B_89]: (k2_pre_topc('#skF_1', B_89)=k2_struct_0('#skF_1') | ~v1_tops_1(B_89, '#skF_1') | ~m1_subset_1(B_89, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_432])).
% 15.86/7.93  tff(c_975, plain, (![A_96]: (k2_pre_topc('#skF_1', A_96)=k2_struct_0('#skF_1') | ~v1_tops_1(A_96, '#skF_1') | ~r1_tarski(A_96, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_797])).
% 15.86/7.93  tff(c_1802, plain, (![A_121]: (k2_pre_topc('#skF_1', A_121)=k2_struct_0('#skF_1') | ~v1_tops_1(A_121, '#skF_1') | k4_xboole_0(A_121, k2_struct_0('#skF_1'))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_975])).
% 15.86/7.93  tff(c_1852, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_499, c_1802])).
% 15.86/7.93  tff(c_2012, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1852])).
% 15.86/7.93  tff(c_269, plain, (![B_56, A_57]: (v1_tops_1(B_56, A_57) | k2_pre_topc(A_57, B_56)!=k2_struct_0(A_57) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_77])).
% 15.86/7.93  tff(c_287, plain, (![B_56]: (v1_tops_1(B_56, '#skF_1') | k2_pre_topc('#skF_1', B_56)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_56, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_269])).
% 15.86/7.93  tff(c_722, plain, (![B_84]: (v1_tops_1(B_84, '#skF_1') | k2_pre_topc('#skF_1', B_84)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_84, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_287])).
% 15.86/7.93  tff(c_896, plain, (![A_93]: (v1_tops_1(A_93, '#skF_1') | k2_pre_topc('#skF_1', A_93)!=k2_struct_0('#skF_1') | ~r1_tarski(A_93, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_722])).
% 15.86/7.93  tff(c_1705, plain, (![A_117]: (v1_tops_1(A_117, '#skF_1') | k2_pre_topc('#skF_1', A_117)!=k2_struct_0('#skF_1') | k4_xboole_0(A_117, k2_struct_0('#skF_1'))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_896])).
% 15.86/7.93  tff(c_1751, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_499, c_1705])).
% 15.86/7.93  tff(c_2019, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2012, c_1751])).
% 15.86/7.93  tff(c_927, plain, (![A_94, B_95]: (k3_subset_1(u1_struct_0(A_94), k2_pre_topc(A_94, k3_subset_1(u1_struct_0(A_94), B_95)))=k1_tops_1(A_94, B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.86/7.93  tff(c_964, plain, (![B_95]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_95)))=k1_tops_1('#skF_1', B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_927])).
% 15.86/7.93  tff(c_971, plain, (![B_95]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_95)))=k1_tops_1('#skF_1', B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_71, c_71, c_964])).
% 15.86/7.93  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(k3_subset_1(A_7, B_8), k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.86/7.93  tff(c_189, plain, (![A_49, B_50]: (m1_subset_1(k2_pre_topc(A_49, B_50), k1_zfmisc_1(u1_struct_0(A_49))) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.86/7.93  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k3_subset_1(A_5, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.86/7.93  tff(c_1974, plain, (![A_131, B_132]: (k4_xboole_0(u1_struct_0(A_131), k2_pre_topc(A_131, B_132))=k3_subset_1(u1_struct_0(A_131), k2_pre_topc(A_131, B_132)) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(resolution, [status(thm)], [c_189, c_12])).
% 15.86/7.93  tff(c_7273, plain, (![A_295, B_296]: (k4_xboole_0(u1_struct_0(A_295), k2_pre_topc(A_295, k3_subset_1(u1_struct_0(A_295), B_296)))=k3_subset_1(u1_struct_0(A_295), k2_pre_topc(A_295, k3_subset_1(u1_struct_0(A_295), B_296))) | ~l1_pre_topc(A_295) | ~m1_subset_1(B_296, k1_zfmisc_1(u1_struct_0(A_295))))), inference(resolution, [status(thm)], [c_14, c_1974])).
% 15.86/7.93  tff(c_1061, plain, (![A_99, B_100]: (r1_tarski(k2_pre_topc(A_99, B_100), u1_struct_0(A_99)) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_189, c_16])).
% 15.86/7.93  tff(c_107, plain, (![B_38, A_39]: (B_38=A_39 | ~r1_tarski(B_38, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.86/7.93  tff(c_115, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_107])).
% 15.86/7.93  tff(c_1077, plain, (![A_99, B_100]: (k2_pre_topc(A_99, B_100)=u1_struct_0(A_99) | k4_xboole_0(u1_struct_0(A_99), k2_pre_topc(A_99, B_100))!=k1_xboole_0 | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_1061, c_115])).
% 15.86/7.93  tff(c_25971, plain, (![A_628, B_629]: (k2_pre_topc(A_628, k3_subset_1(u1_struct_0(A_628), B_629))=u1_struct_0(A_628) | k3_subset_1(u1_struct_0(A_628), k2_pre_topc(A_628, k3_subset_1(u1_struct_0(A_628), B_629)))!=k1_xboole_0 | ~m1_subset_1(k3_subset_1(u1_struct_0(A_628), B_629), k1_zfmisc_1(u1_struct_0(A_628))) | ~l1_pre_topc(A_628) | ~l1_pre_topc(A_628) | ~m1_subset_1(B_629, k1_zfmisc_1(u1_struct_0(A_628))))), inference(superposition, [status(thm), theory('equality')], [c_7273, c_1077])).
% 15.86/7.93  tff(c_26014, plain, (![B_629]: (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_629))=u1_struct_0('#skF_1') | k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_629)))!=k1_xboole_0 | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), B_629), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_629, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_71, c_25971])).
% 15.86/7.93  tff(c_26048, plain, (![B_630]: (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_630))=k2_struct_0('#skF_1') | k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_630)))!=k1_xboole_0 | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), B_630), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_630, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_38, c_38, c_71, c_71, c_71, c_71, c_71, c_26014])).
% 15.86/7.93  tff(c_30565, plain, (![B_677]: (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_677))=k2_struct_0('#skF_1') | k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_677)))!=k1_xboole_0 | ~m1_subset_1(B_677, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_14, c_26048])).
% 15.86/7.93  tff(c_30677, plain, (![B_678]: (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_678))=k2_struct_0('#skF_1') | k1_tops_1('#skF_1', B_678)!=k1_xboole_0 | ~m1_subset_1(B_678, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_678, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_971, c_30565])).
% 15.86/7.93  tff(c_30704, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_72, c_30677])).
% 15.86/7.93  tff(c_30739, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_77, c_30704])).
% 15.86/7.93  tff(c_30741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2019, c_30739])).
% 15.86/7.93  tff(c_30743, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_1852])).
% 15.86/7.93  tff(c_671, plain, (![B_79, A_80]: (v2_tops_1(B_79, A_80) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_80), B_79), A_80) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.86/7.93  tff(c_678, plain, (![B_79]: (v2_tops_1(B_79, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_79), '#skF_1') | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_671])).
% 15.86/7.93  tff(c_680, plain, (![B_79]: (v2_tops_1(B_79, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_79), '#skF_1') | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_71, c_678])).
% 15.86/7.93  tff(c_30766, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_30743, c_680])).
% 15.86/7.93  tff(c_30769, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_30766])).
% 15.86/7.93  tff(c_30771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_30769])).
% 15.86/7.93  tff(c_30773, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 15.86/7.93  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.86/7.93  tff(c_55, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.86/7.93  tff(c_59, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_55])).
% 15.86/7.93  tff(c_30850, plain, (![A_695, B_696]: (k4_xboole_0(A_695, B_696)=k3_subset_1(A_695, B_696) | ~m1_subset_1(B_696, k1_zfmisc_1(A_695)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.86/7.93  tff(c_30882, plain, (![B_699, A_700]: (k4_xboole_0(B_699, A_700)=k3_subset_1(B_699, A_700) | ~r1_tarski(A_700, B_699))), inference(resolution, [status(thm)], [c_18, c_30850])).
% 15.86/7.93  tff(c_30894, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k3_subset_1(B_2, B_2))), inference(resolution, [status(thm)], [c_6, c_30882])).
% 15.86/7.93  tff(c_30900, plain, (![B_2]: (k3_subset_1(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_59, c_30894])).
% 15.86/7.93  tff(c_30772, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 15.86/7.93  tff(c_31453, plain, (![A_736, B_737]: (v1_tops_1(k3_subset_1(u1_struct_0(A_736), B_737), A_736) | ~v2_tops_1(B_737, A_736) | ~m1_subset_1(B_737, k1_zfmisc_1(u1_struct_0(A_736))) | ~l1_pre_topc(A_736))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.86/7.93  tff(c_31463, plain, (![B_737]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_737), '#skF_1') | ~v2_tops_1(B_737, '#skF_1') | ~m1_subset_1(B_737, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_31453])).
% 15.86/7.93  tff(c_31466, plain, (![B_737]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_737), '#skF_1') | ~v2_tops_1(B_737, '#skF_1') | ~m1_subset_1(B_737, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_71, c_31463])).
% 15.86/7.93  tff(c_30833, plain, (![A_691, B_692]: (m1_subset_1(k3_subset_1(A_691, B_692), k1_zfmisc_1(A_691)) | ~m1_subset_1(B_692, k1_zfmisc_1(A_691)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.86/7.93  tff(c_30838, plain, (![A_693, B_694]: (r1_tarski(k3_subset_1(A_693, B_694), A_693) | ~m1_subset_1(B_694, k1_zfmisc_1(A_693)))), inference(resolution, [status(thm)], [c_30833, c_16])).
% 15.86/7.93  tff(c_31236, plain, (![A_724, B_725]: (k4_xboole_0(k3_subset_1(A_724, B_725), A_724)=k1_xboole_0 | ~m1_subset_1(B_725, k1_zfmisc_1(A_724)))), inference(resolution, [status(thm)], [c_30838, c_10])).
% 15.86/7.93  tff(c_31254, plain, (k4_xboole_0(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_31236])).
% 15.86/7.93  tff(c_31094, plain, (![A_714, B_715]: (k2_pre_topc(A_714, B_715)=k2_struct_0(A_714) | ~v1_tops_1(B_715, A_714) | ~m1_subset_1(B_715, k1_zfmisc_1(u1_struct_0(A_714))) | ~l1_pre_topc(A_714))), inference(cnfTransformation, [status(thm)], [f_77])).
% 15.86/7.93  tff(c_31112, plain, (![B_715]: (k2_pre_topc('#skF_1', B_715)=k2_struct_0('#skF_1') | ~v1_tops_1(B_715, '#skF_1') | ~m1_subset_1(B_715, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_31094])).
% 15.86/7.93  tff(c_31166, plain, (![B_719]: (k2_pre_topc('#skF_1', B_719)=k2_struct_0('#skF_1') | ~v1_tops_1(B_719, '#skF_1') | ~m1_subset_1(B_719, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_31112])).
% 15.86/7.93  tff(c_31732, plain, (![A_750]: (k2_pre_topc('#skF_1', A_750)=k2_struct_0('#skF_1') | ~v1_tops_1(A_750, '#skF_1') | ~r1_tarski(A_750, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_31166])).
% 15.86/7.93  tff(c_32466, plain, (![A_771]: (k2_pre_topc('#skF_1', A_771)=k2_struct_0('#skF_1') | ~v1_tops_1(A_771, '#skF_1') | k4_xboole_0(A_771, k2_struct_0('#skF_1'))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_31732])).
% 15.86/7.93  tff(c_32511, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_31254, c_32466])).
% 15.86/7.93  tff(c_32638, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_32511])).
% 15.86/7.93  tff(c_32641, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_31466, c_32638])).
% 15.86/7.93  tff(c_32645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_30772, c_32641])).
% 15.86/7.93  tff(c_32646, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_32511])).
% 15.86/7.93  tff(c_31580, plain, (![A_742, B_743]: (k3_subset_1(u1_struct_0(A_742), k2_pre_topc(A_742, k3_subset_1(u1_struct_0(A_742), B_743)))=k1_tops_1(A_742, B_743) | ~m1_subset_1(B_743, k1_zfmisc_1(u1_struct_0(A_742))) | ~l1_pre_topc(A_742))), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.86/7.93  tff(c_31617, plain, (![B_743]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_743)))=k1_tops_1('#skF_1', B_743) | ~m1_subset_1(B_743, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_31580])).
% 15.86/7.93  tff(c_32867, plain, (![B_790]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_790)))=k1_tops_1('#skF_1', B_790) | ~m1_subset_1(B_790, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_71, c_71, c_31617])).
% 15.86/7.93  tff(c_32911, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_32646, c_32867])).
% 15.86/7.93  tff(c_32919, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_72, c_30900, c_32911])).
% 15.86/7.93  tff(c_32921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30773, c_32919])).
% 15.86/7.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.86/7.93  
% 15.86/7.93  Inference rules
% 15.86/7.93  ----------------------
% 15.86/7.93  #Ref     : 0
% 15.86/7.93  #Sup     : 7768
% 15.86/7.93  #Fact    : 0
% 15.86/7.93  #Define  : 0
% 15.86/7.93  #Split   : 61
% 15.86/7.93  #Chain   : 0
% 15.86/7.93  #Close   : 0
% 15.86/7.93  
% 15.86/7.93  Ordering : KBO
% 15.86/7.93  
% 15.86/7.93  Simplification rules
% 15.86/7.93  ----------------------
% 15.86/7.93  #Subsume      : 2465
% 15.86/7.93  #Demod        : 9236
% 15.86/7.93  #Tautology    : 1776
% 15.86/7.93  #SimpNegUnit  : 657
% 15.86/7.93  #BackRed      : 22
% 15.86/7.93  
% 15.86/7.93  #Partial instantiations: 0
% 15.86/7.93  #Strategies tried      : 1
% 15.86/7.93  
% 15.86/7.93  Timing (in seconds)
% 15.86/7.93  ----------------------
% 15.86/7.94  Preprocessing        : 0.33
% 15.86/7.94  Parsing              : 0.17
% 15.86/7.94  CNF conversion       : 0.02
% 15.86/7.94  Main loop            : 6.83
% 15.86/7.94  Inferencing          : 1.52
% 15.86/7.94  Reduction            : 2.55
% 15.86/7.94  Demodulation         : 1.82
% 15.86/7.94  BG Simplification    : 0.15
% 15.86/7.94  Subsumption          : 2.22
% 15.86/7.94  Abstraction          : 0.23
% 15.86/7.94  MUC search           : 0.00
% 15.86/7.94  Cooper               : 0.00
% 15.86/7.94  Total                : 7.20
% 15.86/7.94  Index Insertion      : 0.00
% 15.86/7.94  Index Deletion       : 0.00
% 15.86/7.94  Index Matching       : 0.00
% 15.86/7.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
