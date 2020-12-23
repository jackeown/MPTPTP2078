%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:34 EST 2020

% Result     : Theorem 8.58s
% Output     : CNFRefutation 8.58s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 151 expanded)
%              Number of leaves         :   36 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  143 ( 294 expanded)
%              Number of equality atoms :   53 (  87 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_118,negated_conjecture,(
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

tff(f_78,axiom,(
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

tff(f_106,axiom,(
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

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_17456,plain,(
    ! [A_352,B_353,C_354] :
      ( k7_subset_1(A_352,B_353,C_354) = k4_xboole_0(B_353,C_354)
      | ~ m1_subset_1(B_353,k1_zfmisc_1(A_352)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_17464,plain,(
    ! [C_354] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_354) = k4_xboole_0('#skF_2',C_354) ),
    inference(resolution,[status(thm)],[c_40,c_17456])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_76,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1231,plain,(
    ! [B_125,A_126] :
      ( v4_pre_topc(B_125,A_126)
      | k2_pre_topc(A_126,B_125) != B_125
      | ~ v2_pre_topc(A_126)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1241,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1231])).

tff(c_1250,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_1241])).

tff(c_1251,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1250])).

tff(c_1527,plain,(
    ! [A_133,B_134] :
      ( k4_subset_1(u1_struct_0(A_133),B_134,k2_tops_1(A_133,B_134)) = k2_pre_topc(A_133,B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1534,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1527])).

tff(c_1542,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1534])).

tff(c_8,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_74,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_82,plain,(
    ! [B_47,A_48] :
      ( B_47 = A_48
      | ~ r1_tarski(B_47,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ r1_tarski(A_49,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_74,c_82])).

tff(c_125,plain,(
    ! [B_52] : k4_xboole_0(k1_xboole_0,B_52) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_98])).

tff(c_14,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_130,plain,(
    ! [B_52] : k5_xboole_0(B_52,k1_xboole_0) = k2_xboole_0(B_52,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_14])).

tff(c_137,plain,(
    ! [B_52] : k5_xboole_0(B_52,k1_xboole_0) = B_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_130])).

tff(c_364,plain,(
    ! [A_76,B_77,C_78] :
      ( k7_subset_1(A_76,B_77,C_78) = k4_xboole_0(B_77,C_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_396,plain,(
    ! [C_83] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_83) = k4_xboole_0('#skF_2',C_83) ),
    inference(resolution,[status(thm)],[c_40,c_364])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_150,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_52])).

tff(c_402,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_150])).

tff(c_429,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_10])).

tff(c_167,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(k4_xboole_0(A_56,B_57),C_58)
      | ~ r1_tarski(A_56,k2_xboole_0(B_57,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_74,c_82])).

tff(c_175,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k1_xboole_0
      | ~ r1_tarski(A_56,k2_xboole_0(B_57,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_167,c_92])).

tff(c_183,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k1_xboole_0
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_175])).

tff(c_439,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_429,c_183])).

tff(c_456,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_14])).

tff(c_466,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_456])).

tff(c_475,plain,(
    ! [A_84,B_85] :
      ( m1_subset_1(k2_tops_1(A_84,B_85),k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_488,plain,(
    ! [A_84,B_85] :
      ( r1_tarski(k2_tops_1(A_84,B_85),u1_struct_0(A_84))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_475,c_22])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1067,plain,(
    ! [A_113,B_114,C_115] :
      ( k4_subset_1(A_113,B_114,C_115) = k2_xboole_0(B_114,C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(A_113))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5056,plain,(
    ! [B_184,B_185,A_186] :
      ( k4_subset_1(B_184,B_185,A_186) = k2_xboole_0(B_185,A_186)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(B_184))
      | ~ r1_tarski(A_186,B_184) ) ),
    inference(resolution,[status(thm)],[c_24,c_1067])).

tff(c_5214,plain,(
    ! [A_192] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_192) = k2_xboole_0('#skF_2',A_192)
      | ~ r1_tarski(A_192,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_40,c_5056])).

tff(c_5218,plain,(
    ! [B_85] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_85)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_85))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_488,c_5214])).

tff(c_17146,plain,(
    ! [B_320] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_320)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_320))
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5218])).

tff(c_17157,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_17146])).

tff(c_17167,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1542,c_466,c_17157])).

tff(c_17169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1251,c_17167])).

tff(c_17170,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_17474,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17464,c_17170])).

tff(c_17171,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_17484,plain,(
    ! [A_358,B_359] :
      ( k2_pre_topc(A_358,B_359) = B_359
      | ~ v4_pre_topc(B_359,A_358)
      | ~ m1_subset_1(B_359,k1_zfmisc_1(u1_struct_0(A_358)))
      | ~ l1_pre_topc(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_17491,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_17484])).

tff(c_17499,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_17171,c_17491])).

tff(c_21580,plain,(
    ! [A_457,B_458] :
      ( k7_subset_1(u1_struct_0(A_457),k2_pre_topc(A_457,B_458),k1_tops_1(A_457,B_458)) = k2_tops_1(A_457,B_458)
      | ~ m1_subset_1(B_458,k1_zfmisc_1(u1_struct_0(A_457)))
      | ~ l1_pre_topc(A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_21589,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_17499,c_21580])).

tff(c_21593,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_17464,c_21589])).

tff(c_21595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17474,c_21593])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:50:12 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.58/3.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.58/3.33  
% 8.58/3.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.58/3.34  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.58/3.34  
% 8.58/3.34  %Foreground sorts:
% 8.58/3.34  
% 8.58/3.34  
% 8.58/3.34  %Background operators:
% 8.58/3.34  
% 8.58/3.34  
% 8.58/3.34  %Foreground operators:
% 8.58/3.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.58/3.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.58/3.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.58/3.34  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.58/3.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.58/3.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.58/3.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.58/3.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.58/3.34  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.58/3.34  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.58/3.34  tff('#skF_2', type, '#skF_2': $i).
% 8.58/3.34  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.58/3.34  tff('#skF_1', type, '#skF_1': $i).
% 8.58/3.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.58/3.34  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.58/3.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.58/3.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.58/3.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.58/3.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.58/3.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.58/3.34  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.58/3.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.58/3.34  
% 8.58/3.37  tff(f_118, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 8.58/3.37  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.58/3.37  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 8.58/3.37  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 8.58/3.37  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 8.58/3.37  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.58/3.37  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 8.58/3.37  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.58/3.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.58/3.37  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.58/3.37  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 8.58/3.37  tff(f_84, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 8.58/3.37  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.58/3.37  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 8.58/3.37  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.58/3.37  tff(c_17456, plain, (![A_352, B_353, C_354]: (k7_subset_1(A_352, B_353, C_354)=k4_xboole_0(B_353, C_354) | ~m1_subset_1(B_353, k1_zfmisc_1(A_352)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.58/3.37  tff(c_17464, plain, (![C_354]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_354)=k4_xboole_0('#skF_2', C_354))), inference(resolution, [status(thm)], [c_40, c_17456])).
% 8.58/3.37  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.58/3.37  tff(c_76, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 8.58/3.37  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.58/3.37  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.58/3.37  tff(c_1231, plain, (![B_125, A_126]: (v4_pre_topc(B_125, A_126) | k2_pre_topc(A_126, B_125)!=B_125 | ~v2_pre_topc(A_126) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.58/3.37  tff(c_1241, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1231])).
% 8.58/3.37  tff(c_1250, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_1241])).
% 8.58/3.37  tff(c_1251, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_76, c_1250])).
% 8.58/3.37  tff(c_1527, plain, (![A_133, B_134]: (k4_subset_1(u1_struct_0(A_133), B_134, k2_tops_1(A_133, B_134))=k2_pre_topc(A_133, B_134) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.58/3.37  tff(c_1534, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1527])).
% 8.58/3.37  tff(c_1542, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1534])).
% 8.58/3.37  tff(c_8, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.58/3.37  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.58/3.37  tff(c_20, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.58/3.37  tff(c_66, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.58/3.37  tff(c_74, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(resolution, [status(thm)], [c_20, c_66])).
% 8.58/3.37  tff(c_82, plain, (![B_47, A_48]: (B_47=A_48 | ~r1_tarski(B_47, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.58/3.37  tff(c_98, plain, (![A_49]: (k1_xboole_0=A_49 | ~r1_tarski(A_49, k1_xboole_0))), inference(resolution, [status(thm)], [c_74, c_82])).
% 8.58/3.37  tff(c_125, plain, (![B_52]: (k4_xboole_0(k1_xboole_0, B_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_98])).
% 8.58/3.37  tff(c_14, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.58/3.37  tff(c_130, plain, (![B_52]: (k5_xboole_0(B_52, k1_xboole_0)=k2_xboole_0(B_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_125, c_14])).
% 8.58/3.37  tff(c_137, plain, (![B_52]: (k5_xboole_0(B_52, k1_xboole_0)=B_52)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_130])).
% 8.58/3.37  tff(c_364, plain, (![A_76, B_77, C_78]: (k7_subset_1(A_76, B_77, C_78)=k4_xboole_0(B_77, C_78) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.58/3.37  tff(c_396, plain, (![C_83]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_83)=k4_xboole_0('#skF_2', C_83))), inference(resolution, [status(thm)], [c_40, c_364])).
% 8.58/3.37  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.58/3.37  tff(c_150, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_76, c_52])).
% 8.58/3.37  tff(c_402, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_396, c_150])).
% 8.58/3.37  tff(c_429, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_402, c_10])).
% 8.58/3.37  tff(c_167, plain, (![A_56, B_57, C_58]: (r1_tarski(k4_xboole_0(A_56, B_57), C_58) | ~r1_tarski(A_56, k2_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.58/3.37  tff(c_92, plain, (![A_17]: (k1_xboole_0=A_17 | ~r1_tarski(A_17, k1_xboole_0))), inference(resolution, [status(thm)], [c_74, c_82])).
% 8.58/3.37  tff(c_175, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k1_xboole_0 | ~r1_tarski(A_56, k2_xboole_0(B_57, k1_xboole_0)))), inference(resolution, [status(thm)], [c_167, c_92])).
% 8.58/3.37  tff(c_183, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k1_xboole_0 | ~r1_tarski(A_56, B_57))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_175])).
% 8.58/3.37  tff(c_439, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_429, c_183])).
% 8.58/3.37  tff(c_456, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_439, c_14])).
% 8.58/3.37  tff(c_466, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_456])).
% 8.58/3.37  tff(c_475, plain, (![A_84, B_85]: (m1_subset_1(k2_tops_1(A_84, B_85), k1_zfmisc_1(u1_struct_0(A_84))) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.58/3.37  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.58/3.37  tff(c_488, plain, (![A_84, B_85]: (r1_tarski(k2_tops_1(A_84, B_85), u1_struct_0(A_84)) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_475, c_22])).
% 8.58/3.37  tff(c_24, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.58/3.37  tff(c_1067, plain, (![A_113, B_114, C_115]: (k4_subset_1(A_113, B_114, C_115)=k2_xboole_0(B_114, C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(A_113)) | ~m1_subset_1(B_114, k1_zfmisc_1(A_113)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.58/3.37  tff(c_5056, plain, (![B_184, B_185, A_186]: (k4_subset_1(B_184, B_185, A_186)=k2_xboole_0(B_185, A_186) | ~m1_subset_1(B_185, k1_zfmisc_1(B_184)) | ~r1_tarski(A_186, B_184))), inference(resolution, [status(thm)], [c_24, c_1067])).
% 8.58/3.37  tff(c_5214, plain, (![A_192]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_192)=k2_xboole_0('#skF_2', A_192) | ~r1_tarski(A_192, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_5056])).
% 8.58/3.37  tff(c_5218, plain, (![B_85]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_85))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_85)) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_488, c_5214])).
% 8.58/3.37  tff(c_17146, plain, (![B_320]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_320))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_320)) | ~m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5218])).
% 8.58/3.37  tff(c_17157, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_17146])).
% 8.58/3.37  tff(c_17167, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1542, c_466, c_17157])).
% 8.58/3.37  tff(c_17169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1251, c_17167])).
% 8.58/3.37  tff(c_17170, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 8.58/3.37  tff(c_17474, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17464, c_17170])).
% 8.58/3.37  tff(c_17171, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 8.58/3.37  tff(c_17484, plain, (![A_358, B_359]: (k2_pre_topc(A_358, B_359)=B_359 | ~v4_pre_topc(B_359, A_358) | ~m1_subset_1(B_359, k1_zfmisc_1(u1_struct_0(A_358))) | ~l1_pre_topc(A_358))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.58/3.37  tff(c_17491, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_17484])).
% 8.58/3.37  tff(c_17499, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_17171, c_17491])).
% 8.58/3.37  tff(c_21580, plain, (![A_457, B_458]: (k7_subset_1(u1_struct_0(A_457), k2_pre_topc(A_457, B_458), k1_tops_1(A_457, B_458))=k2_tops_1(A_457, B_458) | ~m1_subset_1(B_458, k1_zfmisc_1(u1_struct_0(A_457))) | ~l1_pre_topc(A_457))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.58/3.37  tff(c_21589, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_17499, c_21580])).
% 8.58/3.37  tff(c_21593, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_17464, c_21589])).
% 8.58/3.37  tff(c_21595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17474, c_21593])).
% 8.58/3.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.58/3.37  
% 8.58/3.37  Inference rules
% 8.58/3.37  ----------------------
% 8.58/3.37  #Ref     : 0
% 8.58/3.37  #Sup     : 4862
% 8.58/3.37  #Fact    : 0
% 8.58/3.37  #Define  : 0
% 8.58/3.37  #Split   : 5
% 8.58/3.37  #Chain   : 0
% 8.58/3.37  #Close   : 0
% 8.58/3.37  
% 8.58/3.37  Ordering : KBO
% 8.58/3.37  
% 8.58/3.37  Simplification rules
% 8.58/3.37  ----------------------
% 8.58/3.37  #Subsume      : 403
% 8.58/3.37  #Demod        : 6671
% 8.58/3.37  #Tautology    : 3927
% 8.58/3.37  #SimpNegUnit  : 7
% 8.58/3.37  #BackRed      : 1
% 8.58/3.37  
% 8.58/3.37  #Partial instantiations: 0
% 8.58/3.37  #Strategies tried      : 1
% 8.58/3.37  
% 8.58/3.37  Timing (in seconds)
% 8.58/3.37  ----------------------
% 8.58/3.37  Preprocessing        : 0.33
% 8.58/3.37  Parsing              : 0.18
% 8.58/3.37  CNF conversion       : 0.02
% 8.58/3.37  Main loop            : 2.25
% 8.58/3.37  Inferencing          : 0.62
% 8.58/3.37  Reduction            : 0.96
% 8.58/3.38  Demodulation         : 0.77
% 8.58/3.38  BG Simplification    : 0.07
% 8.58/3.38  Subsumption          : 0.50
% 8.58/3.38  Abstraction          : 0.11
% 8.58/3.38  MUC search           : 0.00
% 8.88/3.38  Cooper               : 0.00
% 8.88/3.38  Total                : 2.64
% 8.88/3.38  Index Insertion      : 0.00
% 8.88/3.38  Index Deletion       : 0.00
% 8.88/3.38  Index Matching       : 0.00
% 8.88/3.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
