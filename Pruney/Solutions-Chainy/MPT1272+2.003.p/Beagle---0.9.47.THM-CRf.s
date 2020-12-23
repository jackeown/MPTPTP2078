%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:58 EST 2020

% Result     : Theorem 4.36s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 190 expanded)
%              Number of leaves         :   34 (  79 expanded)
%              Depth                    :   15
%              Number of atoms          :  179 ( 428 expanded)
%              Number of equality atoms :   35 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tops_1(B,A)
             => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_170,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(B_65,k2_tops_1(A_66,B_65))
      | ~ v2_tops_1(B_65,A_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_176,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_170])).

tff(c_181,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_176])).

tff(c_182,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_214,plain,(
    ! [B_71,A_72] :
      ( v2_tops_1(B_71,A_72)
      | ~ r1_tarski(B_71,k2_tops_1(A_72,B_71))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_313,plain,(
    ! [A_88,A_89] :
      ( v2_tops_1(A_88,A_89)
      | ~ m1_subset_1(A_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89)
      | k4_xboole_0(A_88,k2_tops_1(A_89,A_88)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_214])).

tff(c_319,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_313])).

tff(c_324,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_319])).

tff(c_325,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_324])).

tff(c_38,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_220,plain,(
    ! [A_75,B_76] :
      ( v2_tops_1(k2_pre_topc(A_75,B_76),A_75)
      | ~ v3_tops_1(B_76,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_226,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_220])).

tff(c_231,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_226])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k2_pre_topc(A_16,B_17),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_302,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k2_tops_1(A_86,k2_pre_topc(A_86,B_87)),k2_tops_1(A_86,B_87))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_312,plain,(
    ! [A_86,B_87] :
      ( k4_xboole_0(k2_tops_1(A_86,k2_pre_topc(A_86,B_87)),k2_tops_1(A_86,B_87)) = k1_xboole_0
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_302,c_6])).

tff(c_8,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_666,plain,(
    ! [A_122,A_123,B_124] :
      ( r1_tarski(A_122,k2_tops_1(A_123,B_124))
      | ~ r1_tarski(A_122,k2_tops_1(A_123,k2_pre_topc(A_123,B_124)))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_302,c_8])).

tff(c_1526,plain,(
    ! [A_167,A_168,B_169] :
      ( r1_tarski(A_167,k2_tops_1(A_168,B_169))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168)
      | k4_xboole_0(A_167,k2_tops_1(A_168,k2_pre_topc(A_168,B_169))) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_666])).

tff(c_1532,plain,(
    ! [A_167] :
      ( r1_tarski(A_167,k2_tops_1('#skF_1','#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | k4_xboole_0(A_167,k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_1526])).

tff(c_1538,plain,(
    ! [A_170] :
      ( r1_tarski(A_170,k2_tops_1('#skF_1','#skF_2'))
      | k4_xboole_0(A_170,k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1532])).

tff(c_1574,plain,
    ( r1_tarski(k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_1538])).

tff(c_1593,plain,
    ( r1_tarski(k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1574])).

tff(c_1594,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1593])).

tff(c_1597,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_1594])).

tff(c_1601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1597])).

tff(c_1603,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1593])).

tff(c_34,plain,(
    ! [B_34,A_32] :
      ( r1_tarski(B_34,k2_tops_1(A_32,B_34))
      | ~ v2_tops_1(B_34,A_32)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1649,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1603,c_34])).

tff(c_1677,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_231,c_1649])).

tff(c_311,plain,(
    ! [A_5,A_86,B_87] :
      ( r1_tarski(A_5,k2_tops_1(A_86,B_87))
      | ~ r1_tarski(A_5,k2_tops_1(A_86,k2_pre_topc(A_86,B_87)))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_302,c_8])).

tff(c_1680,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1677,c_311])).

tff(c_1692,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1680])).

tff(c_1708,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1692,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k2_tops_1(A_24,B_25),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_183,plain,(
    ! [A_67,B_68,C_69] :
      ( k4_subset_1(A_67,B_68,C_69) = k2_xboole_0(B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_67))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_193,plain,(
    ! [B_70] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_70,'#skF_2') = k2_xboole_0(B_70,'#skF_2')
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_40,c_183])).

tff(c_201,plain,(
    ! [B_25] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',B_25),'#skF_2') = k2_xboole_0(k2_tops_1('#skF_1',B_25),'#skF_2')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_193])).

tff(c_354,plain,(
    ! [B_94] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',B_94),'#skF_2') = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_94))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2,c_201])).

tff(c_372,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_354])).

tff(c_326,plain,(
    ! [A_90,B_91] :
      ( k4_subset_1(u1_struct_0(A_90),B_91,k2_tops_1(A_90,B_91)) = k2_pre_topc(A_90,B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_332,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_326])).

tff(c_337,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_332])).

tff(c_260,plain,(
    ! [A_78,C_79,B_80] :
      ( k4_subset_1(A_78,C_79,B_80) = k4_subset_1(A_78,B_80,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_78))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_270,plain,(
    ! [B_81] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_81,'#skF_2') = k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_40,c_260])).

tff(c_278,plain,(
    ! [B_25] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',B_25),'#skF_2') = k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_25))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_270])).

tff(c_584,plain,(
    ! [B_121] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',B_121),'#skF_2') = k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_121))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_278])).

tff(c_595,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_584])).

tff(c_603,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_337,c_595])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(k2_xboole_0(A_8,B_9),B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_638,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_10])).

tff(c_1733,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1708,c_638])).

tff(c_1735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_325,c_1733])).

tff(c_1737,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_2364,plain,(
    ! [A_224,B_225] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_224),B_225),A_224)
      | ~ v2_tops_1(B_225,A_224)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ l1_pre_topc(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2367,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2364,c_36])).

tff(c_2371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1737,c_2367])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:43:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.36/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.57/1.84  
% 4.57/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.84  %$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.61/1.84  
% 4.61/1.84  %Foreground sorts:
% 4.61/1.84  
% 4.61/1.84  
% 4.61/1.84  %Background operators:
% 4.61/1.84  
% 4.61/1.84  
% 4.61/1.84  %Foreground operators:
% 4.61/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.61/1.84  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.61/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.61/1.84  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.61/1.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.61/1.84  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 4.61/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.61/1.84  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.61/1.84  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.61/1.84  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.61/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.61/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.61/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.61/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.61/1.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.61/1.84  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.61/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.61/1.84  
% 4.61/1.86  tff(f_114, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_tops_1)).
% 4.61/1.86  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 4.61/1.86  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.61/1.86  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 4.61/1.86  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.61/1.86  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tops_1)).
% 4.61/1.86  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.61/1.86  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.61/1.86  tff(f_81, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.61/1.86  tff(f_51, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.61/1.86  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 4.61/1.86  tff(f_45, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 4.61/1.86  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.61/1.86  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 4.61/1.86  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.61/1.86  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.61/1.86  tff(c_170, plain, (![B_65, A_66]: (r1_tarski(B_65, k2_tops_1(A_66, B_65)) | ~v2_tops_1(B_65, A_66) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.61/1.86  tff(c_176, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_170])).
% 4.61/1.86  tff(c_181, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_176])).
% 4.61/1.86  tff(c_182, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_181])).
% 4.61/1.86  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.61/1.86  tff(c_214, plain, (![B_71, A_72]: (v2_tops_1(B_71, A_72) | ~r1_tarski(B_71, k2_tops_1(A_72, B_71)) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.61/1.86  tff(c_313, plain, (![A_88, A_89]: (v2_tops_1(A_88, A_89) | ~m1_subset_1(A_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89) | k4_xboole_0(A_88, k2_tops_1(A_89, A_88))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_214])).
% 4.61/1.86  tff(c_319, plain, (v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_313])).
% 4.61/1.86  tff(c_324, plain, (v2_tops_1('#skF_2', '#skF_1') | k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_319])).
% 4.61/1.86  tff(c_325, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_182, c_324])).
% 4.61/1.86  tff(c_38, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.61/1.86  tff(c_220, plain, (![A_75, B_76]: (v2_tops_1(k2_pre_topc(A_75, B_76), A_75) | ~v3_tops_1(B_76, A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.61/1.86  tff(c_226, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_220])).
% 4.61/1.86  tff(c_231, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_226])).
% 4.61/1.86  tff(c_16, plain, (![A_16, B_17]: (m1_subset_1(k2_pre_topc(A_16, B_17), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.61/1.86  tff(c_302, plain, (![A_86, B_87]: (r1_tarski(k2_tops_1(A_86, k2_pre_topc(A_86, B_87)), k2_tops_1(A_86, B_87)) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.61/1.86  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.61/1.86  tff(c_312, plain, (![A_86, B_87]: (k4_xboole_0(k2_tops_1(A_86, k2_pre_topc(A_86, B_87)), k2_tops_1(A_86, B_87))=k1_xboole_0 | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_302, c_6])).
% 4.61/1.86  tff(c_8, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.61/1.86  tff(c_666, plain, (![A_122, A_123, B_124]: (r1_tarski(A_122, k2_tops_1(A_123, B_124)) | ~r1_tarski(A_122, k2_tops_1(A_123, k2_pre_topc(A_123, B_124))) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_302, c_8])).
% 4.61/1.86  tff(c_1526, plain, (![A_167, A_168, B_169]: (r1_tarski(A_167, k2_tops_1(A_168, B_169)) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168) | k4_xboole_0(A_167, k2_tops_1(A_168, k2_pre_topc(A_168, B_169)))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_666])).
% 4.61/1.86  tff(c_1532, plain, (![A_167]: (r1_tarski(A_167, k2_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | k4_xboole_0(A_167, k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_1526])).
% 4.61/1.86  tff(c_1538, plain, (![A_170]: (r1_tarski(A_170, k2_tops_1('#skF_1', '#skF_2')) | k4_xboole_0(A_170, k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1532])).
% 4.61/1.86  tff(c_1574, plain, (r1_tarski(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_312, c_1538])).
% 4.61/1.86  tff(c_1593, plain, (r1_tarski(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1574])).
% 4.61/1.86  tff(c_1594, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1593])).
% 4.61/1.86  tff(c_1597, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_1594])).
% 4.61/1.86  tff(c_1601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1597])).
% 4.61/1.86  tff(c_1603, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1593])).
% 4.61/1.86  tff(c_34, plain, (![B_34, A_32]: (r1_tarski(B_34, k2_tops_1(A_32, B_34)) | ~v2_tops_1(B_34, A_32) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.61/1.86  tff(c_1649, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1603, c_34])).
% 4.61/1.86  tff(c_1677, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_231, c_1649])).
% 4.61/1.86  tff(c_311, plain, (![A_5, A_86, B_87]: (r1_tarski(A_5, k2_tops_1(A_86, B_87)) | ~r1_tarski(A_5, k2_tops_1(A_86, k2_pre_topc(A_86, B_87))) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_302, c_8])).
% 4.61/1.86  tff(c_1680, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1677, c_311])).
% 4.61/1.86  tff(c_1692, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1680])).
% 4.61/1.86  tff(c_1708, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1692, c_6])).
% 4.61/1.86  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.61/1.86  tff(c_26, plain, (![A_24, B_25]: (m1_subset_1(k2_tops_1(A_24, B_25), k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.61/1.86  tff(c_183, plain, (![A_67, B_68, C_69]: (k4_subset_1(A_67, B_68, C_69)=k2_xboole_0(B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(A_67)) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.61/1.86  tff(c_193, plain, (![B_70]: (k4_subset_1(u1_struct_0('#skF_1'), B_70, '#skF_2')=k2_xboole_0(B_70, '#skF_2') | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_40, c_183])).
% 4.61/1.86  tff(c_201, plain, (![B_25]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', B_25), '#skF_2')=k2_xboole_0(k2_tops_1('#skF_1', B_25), '#skF_2') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_193])).
% 4.61/1.86  tff(c_354, plain, (![B_94]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', B_94), '#skF_2')=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_94)) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2, c_201])).
% 4.61/1.86  tff(c_372, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_354])).
% 4.61/1.86  tff(c_326, plain, (![A_90, B_91]: (k4_subset_1(u1_struct_0(A_90), B_91, k2_tops_1(A_90, B_91))=k2_pre_topc(A_90, B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.61/1.86  tff(c_332, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_326])).
% 4.61/1.86  tff(c_337, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_332])).
% 4.61/1.86  tff(c_260, plain, (![A_78, C_79, B_80]: (k4_subset_1(A_78, C_79, B_80)=k4_subset_1(A_78, B_80, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(A_78)) | ~m1_subset_1(B_80, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.61/1.86  tff(c_270, plain, (![B_81]: (k4_subset_1(u1_struct_0('#skF_1'), B_81, '#skF_2')=k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_40, c_260])).
% 4.61/1.86  tff(c_278, plain, (![B_25]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', B_25), '#skF_2')=k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_25)) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_270])).
% 4.61/1.86  tff(c_584, plain, (![B_121]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', B_121), '#skF_2')=k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_121)) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_278])).
% 4.61/1.86  tff(c_595, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_584])).
% 4.61/1.86  tff(c_603, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_372, c_337, c_595])).
% 4.61/1.86  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(k2_xboole_0(A_8, B_9), B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.61/1.86  tff(c_638, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_603, c_10])).
% 4.61/1.86  tff(c_1733, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1708, c_638])).
% 4.61/1.86  tff(c_1735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_325, c_1733])).
% 4.61/1.86  tff(c_1737, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_181])).
% 4.61/1.86  tff(c_2364, plain, (![A_224, B_225]: (v1_tops_1(k3_subset_1(u1_struct_0(A_224), B_225), A_224) | ~v2_tops_1(B_225, A_224) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_224))) | ~l1_pre_topc(A_224))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.61/1.86  tff(c_36, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.61/1.86  tff(c_2367, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2364, c_36])).
% 4.61/1.86  tff(c_2371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1737, c_2367])).
% 4.61/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.86  
% 4.61/1.86  Inference rules
% 4.61/1.86  ----------------------
% 4.61/1.86  #Ref     : 0
% 4.61/1.86  #Sup     : 563
% 4.61/1.86  #Fact    : 0
% 4.61/1.86  #Define  : 0
% 4.61/1.86  #Split   : 3
% 4.61/1.86  #Chain   : 0
% 4.61/1.86  #Close   : 0
% 4.61/1.86  
% 4.61/1.86  Ordering : KBO
% 4.61/1.86  
% 4.61/1.86  Simplification rules
% 4.61/1.86  ----------------------
% 4.61/1.86  #Subsume      : 142
% 4.61/1.86  #Demod        : 142
% 4.61/1.86  #Tautology    : 194
% 4.61/1.86  #SimpNegUnit  : 2
% 4.61/1.86  #BackRed      : 2
% 4.61/1.86  
% 4.61/1.86  #Partial instantiations: 0
% 4.61/1.86  #Strategies tried      : 1
% 4.61/1.86  
% 4.61/1.86  Timing (in seconds)
% 4.61/1.86  ----------------------
% 4.61/1.86  Preprocessing        : 0.31
% 4.61/1.86  Parsing              : 0.16
% 4.61/1.86  CNF conversion       : 0.02
% 4.61/1.86  Main loop            : 0.70
% 4.61/1.86  Inferencing          : 0.22
% 4.61/1.86  Reduction            : 0.25
% 4.61/1.86  Demodulation         : 0.20
% 4.61/1.86  BG Simplification    : 0.03
% 4.61/1.86  Subsumption          : 0.15
% 4.61/1.86  Abstraction          : 0.03
% 4.61/1.86  MUC search           : 0.00
% 4.61/1.86  Cooper               : 0.00
% 4.61/1.86  Total                : 1.05
% 4.61/1.86  Index Insertion      : 0.00
% 4.61/1.86  Index Deletion       : 0.00
% 4.61/1.86  Index Matching       : 0.00
% 4.61/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
