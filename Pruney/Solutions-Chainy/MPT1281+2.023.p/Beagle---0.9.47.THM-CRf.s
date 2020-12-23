%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:16 EST 2020

% Result     : Theorem 13.52s
% Output     : CNFRefutation 13.52s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 290 expanded)
%              Number of leaves         :   28 ( 112 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 ( 688 expanded)
%              Number of equality atoms :   26 (  73 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_68,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_295,plain,(
    ! [A_108,B_109] :
      ( k2_pre_topc(A_108,k1_tops_1(A_108,B_109)) = B_109
      | ~ v5_tops_1(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_301,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_295])).

tff(c_306,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_301])).

tff(c_24,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_307,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_24])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k1_tops_1(A_17,B_18),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_461,plain,(
    ! [A_136,B_137] :
      ( r1_tarski(k2_tops_1(A_136,k2_pre_topc(A_136,B_137)),k2_tops_1(A_136,B_137))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_472,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_461])).

tff(c_478,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_472])).

tff(c_479,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_478])).

tff(c_501,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_479])).

tff(c_505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_501])).

tff(c_506,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_584,plain,(
    ! [A_140,B_141] :
      ( k4_subset_1(u1_struct_0(A_140),B_141,k2_tops_1(A_140,B_141)) = k2_pre_topc(A_140,B_141)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_592,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_584])).

tff(c_600,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_592])).

tff(c_18,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_tops_1(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_187,plain,(
    ! [A_86,B_87,C_88] :
      ( k4_subset_1(A_86,B_87,C_88) = k2_xboole_0(B_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(A_86))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1692,plain,(
    ! [A_248,B_249,B_250] :
      ( k4_subset_1(u1_struct_0(A_248),B_249,k2_tops_1(A_248,B_250)) = k2_xboole_0(B_249,k2_tops_1(A_248,B_250))
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ l1_pre_topc(A_248) ) ),
    inference(resolution,[status(thm)],[c_18,c_187])).

tff(c_1700,plain,(
    ! [B_250] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_250)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_250))
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_1692])).

tff(c_1709,plain,(
    ! [B_251] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_251)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_251))
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1700])).

tff(c_1723,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_1709])).

tff(c_1732,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_1723])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    ! [A_32,C_33,B_34] :
      ( r1_tarski(A_32,C_33)
      | ~ r1_tarski(B_34,C_33)
      | ~ r1_tarski(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_32,A_4,B_5] :
      ( r1_tarski(A_32,k2_xboole_0(A_4,B_5))
      | ~ r1_tarski(A_32,A_4) ) ),
    inference(resolution,[status(thm)],[c_4,c_41])).

tff(c_45,plain,(
    ! [A_35,A_36,B_37] :
      ( r1_tarski(A_35,k2_xboole_0(A_36,B_37))
      | ~ r1_tarski(A_35,A_36) ) ),
    inference(resolution,[status(thm)],[c_4,c_41])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_1,A_36,B_37,A_35] :
      ( r1_tarski(A_1,k2_xboole_0(A_36,B_37))
      | ~ r1_tarski(A_1,A_35)
      | ~ r1_tarski(A_35,A_36) ) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_638,plain,(
    ! [A_143,B_144] :
      ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_xboole_0(A_143,B_144))
      | ~ r1_tarski(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),A_143) ) ),
    inference(resolution,[status(thm)],[c_506,c_48])).

tff(c_673,plain,(
    ! [A_4,B_5,B_144] :
      ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_xboole_0(k2_xboole_0(A_4,B_5),B_144))
      | ~ r1_tarski(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),A_4) ) ),
    inference(resolution,[status(thm)],[c_44,c_638])).

tff(c_1761,plain,(
    ! [B_144] :
      ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_xboole_0(k2_pre_topc('#skF_1','#skF_2'),B_144))
      | ~ r1_tarski(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1732,c_673])).

tff(c_4099,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1761])).

tff(c_507,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_425,plain,(
    ! [A_130,C_131,B_132] :
      ( k4_subset_1(A_130,C_131,B_132) = k4_subset_1(A_130,B_132,C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(A_130))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2458,plain,(
    ! [A_281,B_282,B_283] :
      ( k4_subset_1(u1_struct_0(A_281),k1_tops_1(A_281,B_282),B_283) = k4_subset_1(u1_struct_0(A_281),B_283,k1_tops_1(A_281,B_282))
      | ~ m1_subset_1(B_283,k1_zfmisc_1(u1_struct_0(A_281)))
      | ~ m1_subset_1(B_282,k1_zfmisc_1(u1_struct_0(A_281)))
      | ~ l1_pre_topc(A_281) ) ),
    inference(resolution,[status(thm)],[c_16,c_425])).

tff(c_5484,plain,(
    ! [A_451,B_452,B_453] :
      ( k4_subset_1(u1_struct_0(A_451),k2_tops_1(A_451,B_452),k1_tops_1(A_451,B_453)) = k4_subset_1(u1_struct_0(A_451),k1_tops_1(A_451,B_453),k2_tops_1(A_451,B_452))
      | ~ m1_subset_1(B_453,k1_zfmisc_1(u1_struct_0(A_451)))
      | ~ m1_subset_1(B_452,k1_zfmisc_1(u1_struct_0(A_451)))
      | ~ l1_pre_topc(A_451) ) ),
    inference(resolution,[status(thm)],[c_18,c_2458])).

tff(c_1969,plain,(
    ! [A_257,B_258,B_259] :
      ( k4_subset_1(u1_struct_0(A_257),B_258,k1_tops_1(A_257,B_259)) = k2_xboole_0(B_258,k1_tops_1(A_257,B_259))
      | ~ m1_subset_1(B_258,k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ l1_pre_topc(A_257) ) ),
    inference(resolution,[status(thm)],[c_16,c_187])).

tff(c_1982,plain,(
    ! [A_19,B_20,B_259] :
      ( k4_subset_1(u1_struct_0(A_19),k2_tops_1(A_19,B_20),k1_tops_1(A_19,B_259)) = k2_xboole_0(k2_tops_1(A_19,B_20),k1_tops_1(A_19,B_259))
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(resolution,[status(thm)],[c_18,c_1969])).

tff(c_22279,plain,(
    ! [A_1133,B_1134,B_1135] :
      ( k4_subset_1(u1_struct_0(A_1133),k1_tops_1(A_1133,B_1134),k2_tops_1(A_1133,B_1135)) = k2_xboole_0(k2_tops_1(A_1133,B_1135),k1_tops_1(A_1133,B_1134))
      | ~ m1_subset_1(B_1134,k1_zfmisc_1(u1_struct_0(A_1133)))
      | ~ m1_subset_1(B_1135,k1_zfmisc_1(u1_struct_0(A_1133)))
      | ~ l1_pre_topc(A_1133)
      | ~ m1_subset_1(B_1134,k1_zfmisc_1(u1_struct_0(A_1133)))
      | ~ m1_subset_1(B_1135,k1_zfmisc_1(u1_struct_0(A_1133)))
      | ~ l1_pre_topc(A_1133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5484,c_1982])).

tff(c_586,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_507,c_584])).

tff(c_595,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_306,c_586])).

tff(c_22299,plain,
    ( k2_xboole_0(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22279,c_595])).

tff(c_22322,plain,(
    k2_xboole_0(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_507,c_28,c_30,c_507,c_28,c_22299])).

tff(c_22598,plain,(
    r1_tarski(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_22322,c_4])).

tff(c_22612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4099,c_22598])).

tff(c_22614,plain,(
    r1_tarski(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1761])).

tff(c_22821,plain,(
    ! [A_1143] :
      ( r1_tarski(A_1143,'#skF_2')
      | ~ r1_tarski(A_1143,k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_22614,c_2])).

tff(c_22834,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_506,c_22821])).

tff(c_22847,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_22834])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.52/6.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.52/6.07  
% 13.52/6.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.52/6.07  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 13.52/6.07  
% 13.52/6.07  %Foreground sorts:
% 13.52/6.07  
% 13.52/6.07  
% 13.52/6.07  %Background operators:
% 13.52/6.07  
% 13.52/6.07  
% 13.52/6.07  %Foreground operators:
% 13.52/6.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.52/6.07  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 13.52/6.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.52/6.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.52/6.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.52/6.07  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 13.52/6.07  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 13.52/6.07  tff('#skF_2', type, '#skF_2': $i).
% 13.52/6.07  tff('#skF_1', type, '#skF_1': $i).
% 13.52/6.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.52/6.07  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 13.52/6.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.52/6.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.52/6.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.52/6.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.52/6.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.52/6.07  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 13.52/6.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.52/6.07  
% 13.52/6.09  tff(f_92, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 13.52/6.09  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 13.52/6.09  tff(f_62, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 13.52/6.09  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tops_1)).
% 13.52/6.09  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 13.52/6.09  tff(f_68, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 13.52/6.09  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 13.52/6.09  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 13.52/6.09  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 13.52/6.09  tff(f_41, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 13.52/6.09  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.52/6.09  tff(c_26, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.52/6.09  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.52/6.09  tff(c_295, plain, (![A_108, B_109]: (k2_pre_topc(A_108, k1_tops_1(A_108, B_109))=B_109 | ~v5_tops_1(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.52/6.09  tff(c_301, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_295])).
% 13.52/6.09  tff(c_306, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_301])).
% 13.52/6.09  tff(c_24, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.52/6.09  tff(c_307, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_306, c_24])).
% 13.52/6.09  tff(c_16, plain, (![A_17, B_18]: (m1_subset_1(k1_tops_1(A_17, B_18), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.52/6.09  tff(c_461, plain, (![A_136, B_137]: (r1_tarski(k2_tops_1(A_136, k2_pre_topc(A_136, B_137)), k2_tops_1(A_136, B_137)) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.52/6.09  tff(c_472, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_306, c_461])).
% 13.52/6.09  tff(c_478, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_472])).
% 13.52/6.09  tff(c_479, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_478])).
% 13.52/6.09  tff(c_501, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_479])).
% 13.52/6.09  tff(c_505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_501])).
% 13.52/6.09  tff(c_506, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_478])).
% 13.52/6.09  tff(c_584, plain, (![A_140, B_141]: (k4_subset_1(u1_struct_0(A_140), B_141, k2_tops_1(A_140, B_141))=k2_pre_topc(A_140, B_141) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.52/6.09  tff(c_592, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_584])).
% 13.52/6.09  tff(c_600, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_592])).
% 13.52/6.09  tff(c_18, plain, (![A_19, B_20]: (m1_subset_1(k2_tops_1(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.52/6.09  tff(c_187, plain, (![A_86, B_87, C_88]: (k4_subset_1(A_86, B_87, C_88)=k2_xboole_0(B_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(A_86)) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.52/6.09  tff(c_1692, plain, (![A_248, B_249, B_250]: (k4_subset_1(u1_struct_0(A_248), B_249, k2_tops_1(A_248, B_250))=k2_xboole_0(B_249, k2_tops_1(A_248, B_250)) | ~m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0(A_248))) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_248))) | ~l1_pre_topc(A_248))), inference(resolution, [status(thm)], [c_18, c_187])).
% 13.52/6.09  tff(c_1700, plain, (![B_250]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_250))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_250)) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_1692])).
% 13.52/6.09  tff(c_1709, plain, (![B_251]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_251))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_251)) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1700])).
% 13.52/6.09  tff(c_1723, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_1709])).
% 13.52/6.09  tff(c_1732, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_600, c_1723])).
% 13.52/6.09  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.52/6.09  tff(c_41, plain, (![A_32, C_33, B_34]: (r1_tarski(A_32, C_33) | ~r1_tarski(B_34, C_33) | ~r1_tarski(A_32, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.52/6.09  tff(c_44, plain, (![A_32, A_4, B_5]: (r1_tarski(A_32, k2_xboole_0(A_4, B_5)) | ~r1_tarski(A_32, A_4))), inference(resolution, [status(thm)], [c_4, c_41])).
% 13.52/6.09  tff(c_45, plain, (![A_35, A_36, B_37]: (r1_tarski(A_35, k2_xboole_0(A_36, B_37)) | ~r1_tarski(A_35, A_36))), inference(resolution, [status(thm)], [c_4, c_41])).
% 13.52/6.09  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.52/6.09  tff(c_48, plain, (![A_1, A_36, B_37, A_35]: (r1_tarski(A_1, k2_xboole_0(A_36, B_37)) | ~r1_tarski(A_1, A_35) | ~r1_tarski(A_35, A_36))), inference(resolution, [status(thm)], [c_45, c_2])).
% 13.52/6.09  tff(c_638, plain, (![A_143, B_144]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_xboole_0(A_143, B_144)) | ~r1_tarski(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), A_143))), inference(resolution, [status(thm)], [c_506, c_48])).
% 13.52/6.09  tff(c_673, plain, (![A_4, B_5, B_144]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_xboole_0(k2_xboole_0(A_4, B_5), B_144)) | ~r1_tarski(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), A_4))), inference(resolution, [status(thm)], [c_44, c_638])).
% 13.52/6.09  tff(c_1761, plain, (![B_144]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), B_144)) | ~r1_tarski(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1732, c_673])).
% 13.52/6.09  tff(c_4099, plain, (~r1_tarski(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_1761])).
% 13.52/6.09  tff(c_507, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_478])).
% 13.52/6.09  tff(c_425, plain, (![A_130, C_131, B_132]: (k4_subset_1(A_130, C_131, B_132)=k4_subset_1(A_130, B_132, C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(A_130)) | ~m1_subset_1(B_132, k1_zfmisc_1(A_130)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.52/6.09  tff(c_2458, plain, (![A_281, B_282, B_283]: (k4_subset_1(u1_struct_0(A_281), k1_tops_1(A_281, B_282), B_283)=k4_subset_1(u1_struct_0(A_281), B_283, k1_tops_1(A_281, B_282)) | ~m1_subset_1(B_283, k1_zfmisc_1(u1_struct_0(A_281))) | ~m1_subset_1(B_282, k1_zfmisc_1(u1_struct_0(A_281))) | ~l1_pre_topc(A_281))), inference(resolution, [status(thm)], [c_16, c_425])).
% 13.52/6.09  tff(c_5484, plain, (![A_451, B_452, B_453]: (k4_subset_1(u1_struct_0(A_451), k2_tops_1(A_451, B_452), k1_tops_1(A_451, B_453))=k4_subset_1(u1_struct_0(A_451), k1_tops_1(A_451, B_453), k2_tops_1(A_451, B_452)) | ~m1_subset_1(B_453, k1_zfmisc_1(u1_struct_0(A_451))) | ~m1_subset_1(B_452, k1_zfmisc_1(u1_struct_0(A_451))) | ~l1_pre_topc(A_451))), inference(resolution, [status(thm)], [c_18, c_2458])).
% 13.52/6.09  tff(c_1969, plain, (![A_257, B_258, B_259]: (k4_subset_1(u1_struct_0(A_257), B_258, k1_tops_1(A_257, B_259))=k2_xboole_0(B_258, k1_tops_1(A_257, B_259)) | ~m1_subset_1(B_258, k1_zfmisc_1(u1_struct_0(A_257))) | ~m1_subset_1(B_259, k1_zfmisc_1(u1_struct_0(A_257))) | ~l1_pre_topc(A_257))), inference(resolution, [status(thm)], [c_16, c_187])).
% 13.52/6.09  tff(c_1982, plain, (![A_19, B_20, B_259]: (k4_subset_1(u1_struct_0(A_19), k2_tops_1(A_19, B_20), k1_tops_1(A_19, B_259))=k2_xboole_0(k2_tops_1(A_19, B_20), k1_tops_1(A_19, B_259)) | ~m1_subset_1(B_259, k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(resolution, [status(thm)], [c_18, c_1969])).
% 13.52/6.09  tff(c_22279, plain, (![A_1133, B_1134, B_1135]: (k4_subset_1(u1_struct_0(A_1133), k1_tops_1(A_1133, B_1134), k2_tops_1(A_1133, B_1135))=k2_xboole_0(k2_tops_1(A_1133, B_1135), k1_tops_1(A_1133, B_1134)) | ~m1_subset_1(B_1134, k1_zfmisc_1(u1_struct_0(A_1133))) | ~m1_subset_1(B_1135, k1_zfmisc_1(u1_struct_0(A_1133))) | ~l1_pre_topc(A_1133) | ~m1_subset_1(B_1134, k1_zfmisc_1(u1_struct_0(A_1133))) | ~m1_subset_1(B_1135, k1_zfmisc_1(u1_struct_0(A_1133))) | ~l1_pre_topc(A_1133))), inference(superposition, [status(thm), theory('equality')], [c_5484, c_1982])).
% 13.52/6.09  tff(c_586, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_507, c_584])).
% 13.52/6.09  tff(c_595, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_306, c_586])).
% 13.52/6.09  tff(c_22299, plain, (k2_xboole_0(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22279, c_595])).
% 13.52/6.09  tff(c_22322, plain, (k2_xboole_0(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_507, c_28, c_30, c_507, c_28, c_22299])).
% 13.52/6.09  tff(c_22598, plain, (r1_tarski(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_22322, c_4])).
% 13.52/6.09  tff(c_22612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4099, c_22598])).
% 13.52/6.09  tff(c_22614, plain, (r1_tarski(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_1761])).
% 13.52/6.09  tff(c_22821, plain, (![A_1143]: (r1_tarski(A_1143, '#skF_2') | ~r1_tarski(A_1143, k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_22614, c_2])).
% 13.52/6.09  tff(c_22834, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_506, c_22821])).
% 13.52/6.09  tff(c_22847, plain, $false, inference(negUnitSimplification, [status(thm)], [c_307, c_22834])).
% 13.52/6.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.52/6.09  
% 13.52/6.09  Inference rules
% 13.52/6.09  ----------------------
% 13.52/6.09  #Ref     : 0
% 13.52/6.09  #Sup     : 6123
% 13.52/6.09  #Fact    : 0
% 13.52/6.09  #Define  : 0
% 13.52/6.09  #Split   : 32
% 13.52/6.09  #Chain   : 0
% 13.52/6.09  #Close   : 0
% 13.52/6.09  
% 13.52/6.09  Ordering : KBO
% 13.52/6.09  
% 13.52/6.09  Simplification rules
% 13.52/6.09  ----------------------
% 13.52/6.09  #Subsume      : 1598
% 13.52/6.09  #Demod        : 1394
% 13.52/6.09  #Tautology    : 1080
% 13.52/6.09  #SimpNegUnit  : 8
% 13.52/6.09  #BackRed      : 8
% 13.52/6.09  
% 13.52/6.09  #Partial instantiations: 0
% 13.52/6.09  #Strategies tried      : 1
% 13.52/6.09  
% 13.52/6.09  Timing (in seconds)
% 13.52/6.09  ----------------------
% 13.52/6.09  Preprocessing        : 0.31
% 13.52/6.09  Parsing              : 0.16
% 13.52/6.09  CNF conversion       : 0.02
% 13.52/6.09  Main loop            : 5.00
% 13.52/6.09  Inferencing          : 0.79
% 13.52/6.09  Reduction            : 1.67
% 13.52/6.09  Demodulation         : 1.28
% 13.52/6.09  BG Simplification    : 0.10
% 13.52/6.09  Subsumption          : 2.16
% 13.52/6.09  Abstraction          : 0.13
% 13.52/6.09  MUC search           : 0.00
% 13.52/6.09  Cooper               : 0.00
% 13.52/6.09  Total                : 5.34
% 13.52/6.09  Index Insertion      : 0.00
% 13.52/6.09  Index Deletion       : 0.00
% 13.52/6.09  Index Matching       : 0.00
% 13.52/6.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
