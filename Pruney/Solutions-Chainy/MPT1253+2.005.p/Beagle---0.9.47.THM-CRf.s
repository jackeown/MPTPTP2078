%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:52 EST 2020

% Result     : Theorem 7.82s
% Output     : CNFRefutation 7.82s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 179 expanded)
%              Number of leaves         :   41 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  125 ( 331 expanded)
%              Number of equality atoms :   35 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_137,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_81,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_73,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_72,plain,(
    ~ r1_tarski(k2_tops_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_74,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_78,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_3361,plain,(
    ! [A_276,C_277,B_278] :
      ( r1_tarski(k2_pre_topc(A_276,C_277),B_278)
      | ~ r1_tarski(C_277,B_278)
      | ~ v4_pre_topc(B_278,A_276)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(u1_struct_0(A_276)))
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0(A_276)))
      | ~ l1_pre_topc(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3417,plain,(
    ! [B_278] :
      ( r1_tarski(k2_pre_topc('#skF_4','#skF_5'),B_278)
      | ~ r1_tarski('#skF_5',B_278)
      | ~ v4_pre_topc(B_278,'#skF_4')
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_3361])).

tff(c_3890,plain,(
    ! [B_292] :
      ( r1_tarski(k2_pre_topc('#skF_4','#skF_5'),B_292)
      | ~ r1_tarski('#skF_5',B_292)
      | ~ v4_pre_topc(B_292,'#skF_4')
      | ~ m1_subset_1(B_292,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3417])).

tff(c_3970,plain,
    ( r1_tarski(k2_pre_topc('#skF_4','#skF_5'),'#skF_5')
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_3890])).

tff(c_4014,plain,(
    r1_tarski(k2_pre_topc('#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_30,c_3970])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4021,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4014,c_26])).

tff(c_4022,plain,(
    ~ r1_tarski('#skF_5',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4021])).

tff(c_1825,plain,(
    ! [A_219,B_220] :
      ( k4_subset_1(u1_struct_0(A_219),B_220,k2_tops_1(A_219,B_220)) = k2_pre_topc(A_219,B_220)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1866,plain,
    ( k4_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = k2_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_1825])).

tff(c_1894,plain,(
    k4_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = k2_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1866])).

tff(c_428,plain,(
    ! [A_120,B_121] :
      ( k4_xboole_0(A_120,B_121) = k3_subset_1(A_120,B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_445,plain,(
    k4_xboole_0(u1_struct_0('#skF_4'),'#skF_5') = k3_subset_1(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_428])).

tff(c_52,plain,(
    ! [A_36,B_37] : k6_subset_1(A_36,B_37) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48,plain,(
    ! [A_31,B_32] : m1_subset_1(k6_subset_1(A_31,B_32),k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_79,plain,(
    ! [A_31,B_32] : m1_subset_1(k4_xboole_0(A_31,B_32),k1_zfmisc_1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48])).

tff(c_489,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_79])).

tff(c_1655,plain,(
    ! [A_215,B_216] :
      ( k2_tops_1(A_215,k3_subset_1(u1_struct_0(A_215),B_216)) = k2_tops_1(A_215,B_216)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1692,plain,
    ( k2_tops_1('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')) = k2_tops_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_1655])).

tff(c_1716,plain,(
    k2_tops_1('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')) = k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1692])).

tff(c_64,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(k2_tops_1(A_50,B_51),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1720,plain,
    ( m1_subset_1(k2_tops_1('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1716,c_64])).

tff(c_1724,plain,(
    m1_subset_1(k2_tops_1('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_489,c_1720])).

tff(c_60,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1746,plain,(
    r1_tarski(k2_tops_1('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1724,c_60])).

tff(c_62,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(A_48,k1_zfmisc_1(B_49))
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_861,plain,(
    ! [A_168,B_169,C_170] :
      ( k4_subset_1(A_168,B_169,C_170) = k2_xboole_0(B_169,C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(A_168))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(A_168)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5100,plain,(
    ! [B_325,B_326,A_327] :
      ( k4_subset_1(B_325,B_326,A_327) = k2_xboole_0(B_326,A_327)
      | ~ m1_subset_1(B_326,k1_zfmisc_1(B_325))
      | ~ r1_tarski(A_327,B_325) ) ),
    inference(resolution,[status(thm)],[c_62,c_861])).

tff(c_5260,plain,(
    ! [A_330] :
      ( k4_subset_1(u1_struct_0('#skF_4'),'#skF_5',A_330) = k2_xboole_0('#skF_5',A_330)
      | ~ r1_tarski(A_330,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_76,c_5100])).

tff(c_5303,plain,(
    k4_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1746,c_5260])).

tff(c_5371,plain,(
    k2_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = k2_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1894,c_5303])).

tff(c_36,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5470,plain,(
    r1_tarski('#skF_5',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5371,c_36])).

tff(c_5500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4022,c_5470])).

tff(c_5501,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4021])).

tff(c_5510,plain,(
    k4_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5501,c_1894])).

tff(c_6530,plain,(
    ! [B_365,B_366,A_367] :
      ( k4_subset_1(B_365,B_366,A_367) = k2_xboole_0(B_366,A_367)
      | ~ m1_subset_1(B_366,k1_zfmisc_1(B_365))
      | ~ r1_tarski(A_367,B_365) ) ),
    inference(resolution,[status(thm)],[c_62,c_861])).

tff(c_6627,plain,(
    ! [A_368] :
      ( k4_subset_1(u1_struct_0('#skF_4'),'#skF_5',A_368) = k2_xboole_0('#skF_5',A_368)
      | ~ r1_tarski(A_368,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_76,c_6530])).

tff(c_6660,plain,(
    k4_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_tops_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1746,c_6627])).

tff(c_6725,plain,(
    k2_xboole_0('#skF_5',k2_tops_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5510,c_6660])).

tff(c_38,plain,(
    ! [B_21,A_20] : k2_tarski(B_21,A_20) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_136,plain,(
    ! [A_79,B_80] : k3_tarski(k2_tarski(A_79,B_80)) = k2_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_172,plain,(
    ! [B_87,A_88] : k3_tarski(k2_tarski(B_87,A_88)) = k2_xboole_0(A_88,B_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_136])).

tff(c_40,plain,(
    ! [A_22,B_23] : k3_tarski(k2_tarski(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_195,plain,(
    ! [B_89,A_90] : k2_xboole_0(B_89,A_90) = k2_xboole_0(A_90,B_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_40])).

tff(c_210,plain,(
    ! [A_90,B_89] : r1_tarski(A_90,k2_xboole_0(B_89,A_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_36])).

tff(c_6821,plain,(
    r1_tarski(k2_tops_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6725,c_210])).

tff(c_6854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_6821])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:31:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.82/2.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.82/2.76  
% 7.82/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.82/2.76  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 7.82/2.76  
% 7.82/2.76  %Foreground sorts:
% 7.82/2.76  
% 7.82/2.76  
% 7.82/2.76  %Background operators:
% 7.82/2.76  
% 7.82/2.76  
% 7.82/2.76  %Foreground operators:
% 7.82/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.82/2.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.82/2.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.82/2.76  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 7.82/2.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.82/2.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.82/2.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.82/2.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.82/2.76  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.82/2.76  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.82/2.76  tff('#skF_5', type, '#skF_5': $i).
% 7.82/2.76  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 7.82/2.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.82/2.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.82/2.76  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.82/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.82/2.76  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.82/2.76  tff('#skF_4', type, '#skF_4': $i).
% 7.82/2.76  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.82/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.82/2.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.82/2.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.82/2.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.82/2.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.82/2.76  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.82/2.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.82/2.76  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.82/2.76  
% 7.82/2.78  tff(f_147, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 7.82/2.78  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.82/2.78  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_1)).
% 7.82/2.78  tff(f_137, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 7.82/2.78  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 7.82/2.78  tff(f_81, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 7.82/2.78  tff(f_73, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 7.82/2.78  tff(f_130, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 7.82/2.78  tff(f_109, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 7.82/2.78  tff(f_103, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.82/2.78  tff(f_79, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 7.82/2.78  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.82/2.78  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.82/2.78  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.82/2.78  tff(c_72, plain, (~r1_tarski(k2_tops_1('#skF_4', '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.82/2.78  tff(c_74, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.82/2.78  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.82/2.78  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.82/2.78  tff(c_78, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.82/2.78  tff(c_3361, plain, (![A_276, C_277, B_278]: (r1_tarski(k2_pre_topc(A_276, C_277), B_278) | ~r1_tarski(C_277, B_278) | ~v4_pre_topc(B_278, A_276) | ~m1_subset_1(C_277, k1_zfmisc_1(u1_struct_0(A_276))) | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0(A_276))) | ~l1_pre_topc(A_276))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.82/2.78  tff(c_3417, plain, (![B_278]: (r1_tarski(k2_pre_topc('#skF_4', '#skF_5'), B_278) | ~r1_tarski('#skF_5', B_278) | ~v4_pre_topc(B_278, '#skF_4') | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_3361])).
% 7.82/2.78  tff(c_3890, plain, (![B_292]: (r1_tarski(k2_pre_topc('#skF_4', '#skF_5'), B_292) | ~r1_tarski('#skF_5', B_292) | ~v4_pre_topc(B_292, '#skF_4') | ~m1_subset_1(B_292, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3417])).
% 7.82/2.78  tff(c_3970, plain, (r1_tarski(k2_pre_topc('#skF_4', '#skF_5'), '#skF_5') | ~r1_tarski('#skF_5', '#skF_5') | ~v4_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_3890])).
% 7.82/2.78  tff(c_4014, plain, (r1_tarski(k2_pre_topc('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_30, c_3970])).
% 7.82/2.78  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.82/2.78  tff(c_4021, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k2_pre_topc('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4014, c_26])).
% 7.82/2.78  tff(c_4022, plain, (~r1_tarski('#skF_5', k2_pre_topc('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_4021])).
% 7.82/2.78  tff(c_1825, plain, (![A_219, B_220]: (k4_subset_1(u1_struct_0(A_219), B_220, k2_tops_1(A_219, B_220))=k2_pre_topc(A_219, B_220) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_219))) | ~l1_pre_topc(A_219))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.82/2.78  tff(c_1866, plain, (k4_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k2_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_76, c_1825])).
% 7.82/2.78  tff(c_1894, plain, (k4_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k2_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1866])).
% 7.82/2.78  tff(c_428, plain, (![A_120, B_121]: (k4_xboole_0(A_120, B_121)=k3_subset_1(A_120, B_121) | ~m1_subset_1(B_121, k1_zfmisc_1(A_120)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.82/2.78  tff(c_445, plain, (k4_xboole_0(u1_struct_0('#skF_4'), '#skF_5')=k3_subset_1(u1_struct_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_76, c_428])).
% 7.82/2.78  tff(c_52, plain, (![A_36, B_37]: (k6_subset_1(A_36, B_37)=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.82/2.78  tff(c_48, plain, (![A_31, B_32]: (m1_subset_1(k6_subset_1(A_31, B_32), k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.82/2.78  tff(c_79, plain, (![A_31, B_32]: (m1_subset_1(k4_xboole_0(A_31, B_32), k1_zfmisc_1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48])).
% 7.82/2.78  tff(c_489, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_445, c_79])).
% 7.82/2.78  tff(c_1655, plain, (![A_215, B_216]: (k2_tops_1(A_215, k3_subset_1(u1_struct_0(A_215), B_216))=k2_tops_1(A_215, B_216) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.82/2.78  tff(c_1692, plain, (k2_tops_1('#skF_4', k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'))=k2_tops_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_76, c_1655])).
% 7.82/2.78  tff(c_1716, plain, (k2_tops_1('#skF_4', k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'))=k2_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1692])).
% 7.82/2.78  tff(c_64, plain, (![A_50, B_51]: (m1_subset_1(k2_tops_1(A_50, B_51), k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.82/2.78  tff(c_1720, plain, (m1_subset_1(k2_tops_1('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1716, c_64])).
% 7.82/2.78  tff(c_1724, plain, (m1_subset_1(k2_tops_1('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_489, c_1720])).
% 7.82/2.78  tff(c_60, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.82/2.78  tff(c_1746, plain, (r1_tarski(k2_tops_1('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1724, c_60])).
% 7.82/2.78  tff(c_62, plain, (![A_48, B_49]: (m1_subset_1(A_48, k1_zfmisc_1(B_49)) | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.82/2.78  tff(c_861, plain, (![A_168, B_169, C_170]: (k4_subset_1(A_168, B_169, C_170)=k2_xboole_0(B_169, C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(A_168)) | ~m1_subset_1(B_169, k1_zfmisc_1(A_168)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.82/2.78  tff(c_5100, plain, (![B_325, B_326, A_327]: (k4_subset_1(B_325, B_326, A_327)=k2_xboole_0(B_326, A_327) | ~m1_subset_1(B_326, k1_zfmisc_1(B_325)) | ~r1_tarski(A_327, B_325))), inference(resolution, [status(thm)], [c_62, c_861])).
% 7.82/2.78  tff(c_5260, plain, (![A_330]: (k4_subset_1(u1_struct_0('#skF_4'), '#skF_5', A_330)=k2_xboole_0('#skF_5', A_330) | ~r1_tarski(A_330, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_76, c_5100])).
% 7.82/2.78  tff(c_5303, plain, (k4_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1746, c_5260])).
% 7.82/2.78  tff(c_5371, plain, (k2_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k2_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1894, c_5303])).
% 7.82/2.78  tff(c_36, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.82/2.78  tff(c_5470, plain, (r1_tarski('#skF_5', k2_pre_topc('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5371, c_36])).
% 7.82/2.78  tff(c_5500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4022, c_5470])).
% 7.82/2.78  tff(c_5501, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_4021])).
% 7.82/2.78  tff(c_5510, plain, (k4_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5501, c_1894])).
% 7.82/2.78  tff(c_6530, plain, (![B_365, B_366, A_367]: (k4_subset_1(B_365, B_366, A_367)=k2_xboole_0(B_366, A_367) | ~m1_subset_1(B_366, k1_zfmisc_1(B_365)) | ~r1_tarski(A_367, B_365))), inference(resolution, [status(thm)], [c_62, c_861])).
% 7.82/2.78  tff(c_6627, plain, (![A_368]: (k4_subset_1(u1_struct_0('#skF_4'), '#skF_5', A_368)=k2_xboole_0('#skF_5', A_368) | ~r1_tarski(A_368, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_76, c_6530])).
% 7.82/2.78  tff(c_6660, plain, (k4_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_tops_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1746, c_6627])).
% 7.82/2.78  tff(c_6725, plain, (k2_xboole_0('#skF_5', k2_tops_1('#skF_4', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5510, c_6660])).
% 7.82/2.78  tff(c_38, plain, (![B_21, A_20]: (k2_tarski(B_21, A_20)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.82/2.78  tff(c_136, plain, (![A_79, B_80]: (k3_tarski(k2_tarski(A_79, B_80))=k2_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.82/2.78  tff(c_172, plain, (![B_87, A_88]: (k3_tarski(k2_tarski(B_87, A_88))=k2_xboole_0(A_88, B_87))), inference(superposition, [status(thm), theory('equality')], [c_38, c_136])).
% 7.82/2.78  tff(c_40, plain, (![A_22, B_23]: (k3_tarski(k2_tarski(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.82/2.78  tff(c_195, plain, (![B_89, A_90]: (k2_xboole_0(B_89, A_90)=k2_xboole_0(A_90, B_89))), inference(superposition, [status(thm), theory('equality')], [c_172, c_40])).
% 7.82/2.78  tff(c_210, plain, (![A_90, B_89]: (r1_tarski(A_90, k2_xboole_0(B_89, A_90)))), inference(superposition, [status(thm), theory('equality')], [c_195, c_36])).
% 7.82/2.78  tff(c_6821, plain, (r1_tarski(k2_tops_1('#skF_4', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6725, c_210])).
% 7.82/2.78  tff(c_6854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_6821])).
% 7.82/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.82/2.78  
% 7.82/2.78  Inference rules
% 7.82/2.78  ----------------------
% 7.82/2.78  #Ref     : 0
% 7.82/2.78  #Sup     : 1676
% 7.82/2.78  #Fact    : 0
% 7.82/2.78  #Define  : 0
% 7.82/2.78  #Split   : 8
% 7.82/2.78  #Chain   : 0
% 7.82/2.78  #Close   : 0
% 7.82/2.78  
% 7.82/2.78  Ordering : KBO
% 7.82/2.78  
% 7.82/2.78  Simplification rules
% 7.82/2.78  ----------------------
% 7.82/2.78  #Subsume      : 72
% 7.82/2.78  #Demod        : 1007
% 7.82/2.78  #Tautology    : 520
% 7.82/2.78  #SimpNegUnit  : 2
% 7.82/2.78  #BackRed      : 14
% 7.82/2.78  
% 7.82/2.78  #Partial instantiations: 0
% 7.82/2.78  #Strategies tried      : 1
% 7.82/2.78  
% 7.82/2.78  Timing (in seconds)
% 7.82/2.78  ----------------------
% 8.11/2.78  Preprocessing        : 0.36
% 8.11/2.78  Parsing              : 0.19
% 8.11/2.78  CNF conversion       : 0.03
% 8.11/2.78  Main loop            : 1.57
% 8.11/2.78  Inferencing          : 0.40
% 8.11/2.78  Reduction            : 0.72
% 8.11/2.78  Demodulation         : 0.57
% 8.11/2.78  BG Simplification    : 0.06
% 8.11/2.78  Subsumption          : 0.29
% 8.11/2.78  Abstraction          : 0.08
% 8.11/2.79  MUC search           : 0.00
% 8.11/2.79  Cooper               : 0.00
% 8.11/2.79  Total                : 1.97
% 8.11/2.79  Index Insertion      : 0.00
% 8.11/2.79  Index Deletion       : 0.00
% 8.11/2.79  Index Matching       : 0.00
% 8.11/2.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
