%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1266+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:41 EST 2020

% Result     : Theorem 8.63s
% Output     : CNFRefutation 8.96s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 914 expanded)
%              Number of leaves         :   32 ( 319 expanded)
%              Depth                    :   15
%              Number of atoms          :  277 (1891 expanded)
%              Number of equality atoms :   72 ( 504 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_38,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_67,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_22,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_46,plain,(
    ! [A_27] :
      ( u1_struct_0(A_27) = k2_struct_0(A_27)
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_22,c_46])).

tff(c_55,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_51])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_57,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_34])).

tff(c_145,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(k3_subset_1(A_40,B_41),k1_zfmisc_1(A_40))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_157,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k3_subset_1(A_42,B_43),A_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(resolution,[status(thm)],[c_145,c_30])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_352,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(k3_subset_1(A_52,B_53),A_52) = k1_xboole_0
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(resolution,[status(thm)],[c_157,c_28])).

tff(c_372,plain,(
    k4_xboole_0(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_57,c_352])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | k4_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_489,plain,(
    ! [B_61,A_62] :
      ( v1_tops_1(B_61,A_62)
      | k2_pre_topc(A_62,B_61) != k2_struct_0(A_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_506,plain,(
    ! [B_61] :
      ( v1_tops_1(B_61,'#skF_1')
      | k2_pre_topc('#skF_1',B_61) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_489])).

tff(c_568,plain,(
    ! [B_66] :
      ( v1_tops_1(B_66,'#skF_1')
      | k2_pre_topc('#skF_1',B_66) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_506])).

tff(c_790,plain,(
    ! [A_76] :
      ( v1_tops_1(A_76,'#skF_1')
      | k2_pre_topc('#skF_1',A_76) != k2_struct_0('#skF_1')
      | ~ r1_tarski(A_76,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_32,c_568])).

tff(c_1057,plain,(
    ! [A_86] :
      ( v1_tops_1(A_86,'#skF_1')
      | k2_pre_topc('#skF_1',A_86) != k2_struct_0('#skF_1')
      | k4_xboole_0(A_86,k2_struct_0('#skF_1')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_790])).

tff(c_1107,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_1057])).

tff(c_1590,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1107])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k3_subset_1(A_16,B_17),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_594,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_57,c_568])).

tff(c_595,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_594])).

tff(c_598,plain,(
    ! [A_67,B_68] :
      ( k2_pre_topc(A_67,B_68) = k2_struct_0(A_67)
      | ~ v1_tops_1(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_615,plain,(
    ! [B_68] :
      ( k2_pre_topc('#skF_1',B_68) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_68,'#skF_1')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_598])).

tff(c_662,plain,(
    ! [B_70] :
      ( k2_pre_topc('#skF_1',B_70) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_70,'#skF_1')
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_615])).

tff(c_682,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_57,c_662])).

tff(c_694,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_595,c_682])).

tff(c_223,plain,(
    ! [A_46,B_47] :
      ( k3_subset_1(A_46,k3_subset_1(A_46,B_47)) = B_47
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_242,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_57,c_223])).

tff(c_747,plain,(
    ! [A_73,B_74] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_73),B_74),A_73)
      | ~ v2_tops_1(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_757,plain,(
    ! [B_74] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_74),'#skF_1')
      | ~ v2_tops_1(B_74,'#skF_1')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_747])).

tff(c_1305,plain,(
    ! [B_93] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_93),'#skF_1')
      | ~ v2_tops_1(B_93,'#skF_1')
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_55,c_757])).

tff(c_1316,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_1305])).

tff(c_1323,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_694,c_1316])).

tff(c_1480,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1323])).

tff(c_1483,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_20,c_1480])).

tff(c_1490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_1483])).

tff(c_1492,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1323])).

tff(c_91,plain,(
    ! [A_37] :
      ( m1_subset_1(k2_struct_0(A_37),k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_99,plain,(
    ! [A_38] :
      ( r1_tarski(k2_struct_0(A_38),u1_struct_0(A_38))
      | ~ l1_struct_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_91,c_30])).

tff(c_105,plain,
    ( r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_99])).

tff(c_107,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_111,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_107])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_111])).

tff(c_116,plain,(
    r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_126,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_116,c_28])).

tff(c_117,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_97,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_91])).

tff(c_151,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_97])).

tff(c_162,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = k3_subset_1(A_44,B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_165,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_151,c_162])).

tff(c_179,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_165])).

tff(c_227,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_151,c_223])).

tff(c_238,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_227])).

tff(c_1544,plain,(
    r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1492,c_30])).

tff(c_44,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_86,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_44])).

tff(c_241,plain,(
    ! [B_24,A_23] :
      ( k3_subset_1(B_24,k3_subset_1(B_24,A_23)) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_32,c_223])).

tff(c_1114,plain,(
    ! [A_87,B_88] :
      ( k3_subset_1(u1_struct_0(A_87),k2_pre_topc(A_87,k3_subset_1(u1_struct_0(A_87),B_88))) = k1_tops_1(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9997,plain,(
    ! [A_252,A_253] :
      ( k3_subset_1(u1_struct_0(A_252),k2_pre_topc(A_252,A_253)) = k1_tops_1(A_252,k3_subset_1(u1_struct_0(A_252),A_253))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_252),A_253),k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ l1_pre_topc(A_252)
      | ~ r1_tarski(A_253,u1_struct_0(A_252)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_1114])).

tff(c_10035,plain,(
    ! [A_253] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_253)) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),A_253))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),A_253),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_253,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_9997])).

tff(c_10441,plain,(
    ! [A_258] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_258)) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),A_258))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),A_258),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ r1_tarski(A_258,k2_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_36,c_55,c_55,c_55,c_10035])).

tff(c_10505,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_10441])).

tff(c_10544,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1544,c_57,c_86,c_242,c_10505])).

tff(c_415,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k2_pre_topc(A_56,B_57),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( k3_subset_1(A_19,k3_subset_1(A_19,B_20)) = B_20
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1601,plain,(
    ! [A_108,B_109] :
      ( k3_subset_1(u1_struct_0(A_108),k3_subset_1(u1_struct_0(A_108),k2_pre_topc(A_108,B_109))) = k2_pre_topc(A_108,B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_415,c_24])).

tff(c_1658,plain,(
    ! [B_109] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_109))) = k2_pre_topc('#skF_1',B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_1601])).

tff(c_1669,plain,(
    ! [B_109] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_109))) = k2_pre_topc('#skF_1',B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_55,c_55,c_1658])).

tff(c_10627,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0)
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10544,c_1669])).

tff(c_10712,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1492,c_238,c_10627])).

tff(c_10714,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1590,c_10712])).

tff(c_10715,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_1107])).

tff(c_930,plain,(
    ! [B_79,A_80] :
      ( v2_tops_1(B_79,A_80)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_80),B_79),A_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_943,plain,(
    ! [B_79] :
      ( v2_tops_1(B_79,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_79),'#skF_1')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_930])).

tff(c_946,plain,(
    ! [B_79] :
      ( v2_tops_1(B_79,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_79),'#skF_1')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_55,c_943])).

tff(c_10719,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_10715,c_946])).

tff(c_10722,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_10719])).

tff(c_10724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_10722])).

tff(c_10725,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_10747,plain,(
    ! [A_263] :
      ( m1_subset_1(k2_struct_0(A_263),k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ l1_struct_0(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10755,plain,(
    ! [A_264] :
      ( r1_tarski(k2_struct_0(A_264),u1_struct_0(A_264))
      | ~ l1_struct_0(A_264) ) ),
    inference(resolution,[status(thm)],[c_10747,c_30])).

tff(c_10761,plain,
    ( r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_10755])).

tff(c_10763,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_10761])).

tff(c_10766,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_10763])).

tff(c_10770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_10766])).

tff(c_10771,plain,(
    r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_10761])).

tff(c_10781,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10771,c_28])).

tff(c_10772,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_10761])).

tff(c_10753,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_10747])).

tff(c_10814,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10772,c_10753])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k3_subset_1(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10817,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10814,c_14])).

tff(c_10822,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10781,c_10817])).

tff(c_10726,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_11531,plain,(
    ! [A_305,B_306] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_305),B_306),A_305)
      | ~ v2_tops_1(B_306,A_305)
      | ~ m1_subset_1(B_306,k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ l1_pre_topc(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_11544,plain,(
    ! [B_306] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_306),'#skF_1')
      | ~ v2_tops_1(B_306,'#skF_1')
      | ~ m1_subset_1(B_306,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_11531])).

tff(c_11547,plain,(
    ! [B_306] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_306),'#skF_1')
      | ~ v2_tops_1(B_306,'#skF_1')
      | ~ m1_subset_1(B_306,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_55,c_11544])).

tff(c_10852,plain,(
    ! [A_270,B_271] :
      ( m1_subset_1(k3_subset_1(A_270,B_271),k1_zfmisc_1(A_270))
      | ~ m1_subset_1(B_271,k1_zfmisc_1(A_270)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10930,plain,(
    ! [A_274,B_275] :
      ( r1_tarski(k3_subset_1(A_274,B_275),A_274)
      | ~ m1_subset_1(B_275,k1_zfmisc_1(A_274)) ) ),
    inference(resolution,[status(thm)],[c_10852,c_30])).

tff(c_11042,plain,(
    ! [A_282,B_283] :
      ( k4_xboole_0(k3_subset_1(A_282,B_283),A_282) = k1_xboole_0
      | ~ m1_subset_1(B_283,k1_zfmisc_1(A_282)) ) ),
    inference(resolution,[status(thm)],[c_10930,c_28])).

tff(c_11065,plain,(
    k4_xboole_0(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_57,c_11042])).

tff(c_11124,plain,(
    ! [A_286,B_287] :
      ( k2_pre_topc(A_286,B_287) = k2_struct_0(A_286)
      | ~ v1_tops_1(B_287,A_286)
      | ~ m1_subset_1(B_287,k1_zfmisc_1(u1_struct_0(A_286)))
      | ~ l1_pre_topc(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_11141,plain,(
    ! [B_287] :
      ( k2_pre_topc('#skF_1',B_287) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_287,'#skF_1')
      | ~ m1_subset_1(B_287,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_11124])).

tff(c_11500,plain,(
    ! [B_304] :
      ( k2_pre_topc('#skF_1',B_304) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_304,'#skF_1')
      | ~ m1_subset_1(B_304,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_11141])).

tff(c_11549,plain,(
    ! [A_307] :
      ( k2_pre_topc('#skF_1',A_307) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(A_307,'#skF_1')
      | ~ r1_tarski(A_307,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_32,c_11500])).

tff(c_11671,plain,(
    ! [A_312] :
      ( k2_pre_topc('#skF_1',A_312) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(A_312,'#skF_1')
      | k4_xboole_0(A_312,k2_struct_0('#skF_1')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_11549])).

tff(c_11717,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_11065,c_11671])).

tff(c_12066,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_11717])).

tff(c_12069,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_11547,c_12066])).

tff(c_12073,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_10726,c_12069])).

tff(c_12074,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_11717])).

tff(c_11725,plain,(
    ! [A_313,B_314] :
      ( k3_subset_1(u1_struct_0(A_313),k2_pre_topc(A_313,k3_subset_1(u1_struct_0(A_313),B_314))) = k1_tops_1(A_313,B_314)
      | ~ m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0(A_313)))
      | ~ l1_pre_topc(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_11774,plain,(
    ! [B_314] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_314))) = k1_tops_1('#skF_1',B_314)
      | ~ m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_11725])).

tff(c_12311,plain,(
    ! [B_337] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_337))) = k1_tops_1('#skF_1',B_337)
      | ~ m1_subset_1(B_337,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_55,c_55,c_11774])).

tff(c_12353,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12074,c_12311])).

tff(c_12374,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_10822,c_12353])).

tff(c_12376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10725,c_12374])).

%------------------------------------------------------------------------------
