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
% DateTime   : Thu Dec  3 10:20:24 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  124 (1086 expanded)
%              Number of leaves         :   31 ( 380 expanded)
%              Depth                    :   20
%              Number of atoms          :  247 (2260 expanded)
%              Number of equality atoms :   54 ( 566 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_subset_1 > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( k2_struct_0(A) = k4_subset_1(u1_struct_0(A),B,C)
                  & r1_xboole_0(B,C) )
               => C = k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_55,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_26,c_55])).

tff(c_64,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_60])).

tff(c_34,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_70,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_34])).

tff(c_71,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_65,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_30])).

tff(c_40,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_87,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_40])).

tff(c_88,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_87])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_72,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_80,plain,(
    ! [A_4] : r1_tarski(A_4,A_4) ),
    inference(resolution,[status(thm)],[c_41,c_72])).

tff(c_95,plain,(
    ! [B_44,C_45,A_46] :
      ( r1_xboole_0(B_44,C_45)
      | ~ r1_tarski(B_44,k3_subset_1(A_46,C_45))
      | ~ m1_subset_1(C_45,k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_189,plain,(
    ! [A_57,C_58] :
      ( r1_xboole_0(k3_subset_1(A_57,C_58),C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(A_57))
      | ~ m1_subset_1(k3_subset_1(A_57,C_58),k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_80,c_95])).

tff(c_197,plain,(
    ! [A_59,B_60] :
      ( r1_xboole_0(k3_subset_1(A_59,B_60),B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(resolution,[status(thm)],[c_8,c_189])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_200,plain,(
    ! [B_60,A_59] :
      ( r1_xboole_0(B_60,k3_subset_1(A_59,B_60))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(resolution,[status(thm)],[c_197,c_2])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k4_subset_1(A_7,B_8,k3_subset_1(A_7,B_8)) = k2_subset_1(A_7)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_106,plain,(
    ! [A_47,B_48] :
      ( k4_subset_1(A_47,B_48,k3_subset_1(A_47,B_48)) = A_47
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_117,plain,(
    k4_subset_1(k2_struct_0('#skF_1'),'#skF_2',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_65,c_106])).

tff(c_232,plain,(
    ! [A_72,B_73,C_74] :
      ( k7_subset_1(u1_struct_0(A_72),k2_struct_0(A_72),B_73) = C_74
      | ~ r1_xboole_0(B_73,C_74)
      | k4_subset_1(u1_struct_0(A_72),B_73,C_74) != k2_struct_0(A_72)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_243,plain,(
    ! [B_73,C_74] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_73) = C_74
      | ~ r1_xboole_0(B_73,C_74)
      | k4_subset_1(k2_struct_0('#skF_1'),B_73,C_74) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_232])).

tff(c_246,plain,(
    ! [B_73,C_74] :
      ( k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_73) = C_74
      | ~ r1_xboole_0(B_73,C_74)
      | k4_subset_1(k2_struct_0('#skF_1'),B_73,C_74) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_64,c_243])).

tff(c_252,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_255,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_252])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_255])).

tff(c_267,plain,(
    ! [B_78,C_79] :
      ( k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_78) = C_79
      | ~ r1_xboole_0(B_78,C_79)
      | k4_subset_1(k2_struct_0('#skF_1'),B_78,C_79) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_272,plain,
    ( k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')
    | ~ r1_xboole_0('#skF_2',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_267])).

tff(c_282,plain,
    ( k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')
    | ~ r1_xboole_0('#skF_2',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_272])).

tff(c_287,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_282])).

tff(c_290,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_287])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_290])).

tff(c_298,plain,
    ( ~ r1_xboole_0('#skF_2',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_333,plain,(
    ~ r1_xboole_0('#skF_2',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_336,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_200,c_333])).

tff(c_340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_336])).

tff(c_341,plain,(
    k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_212,plain,(
    ! [B_66,A_67] :
      ( v4_pre_topc(B_66,A_67)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_67),k2_struct_0(A_67),B_66),A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_218,plain,(
    ! [B_66] :
      ( v4_pre_topc(B_66,'#skF_1')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_66),'#skF_1')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_212])).

tff(c_221,plain,(
    ! [B_66] :
      ( v4_pre_topc(B_66,'#skF_1')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_66),'#skF_1')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_64,c_218])).

tff(c_386,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_221])).

tff(c_393,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_88,c_386])).

tff(c_395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_393])).

tff(c_396,plain,(
    ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_397,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_400,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(A_85,B_86)
      | ~ m1_subset_1(A_85,k1_zfmisc_1(B_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_412,plain,(
    ! [A_4] : r1_tarski(A_4,A_4) ),
    inference(resolution,[status(thm)],[c_41,c_400])).

tff(c_499,plain,(
    ! [B_102,C_103,A_104] :
      ( r1_xboole_0(B_102,C_103)
      | ~ r1_tarski(B_102,k3_subset_1(A_104,C_103))
      | ~ m1_subset_1(C_103,k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_514,plain,(
    ! [A_105,C_106] :
      ( r1_xboole_0(k3_subset_1(A_105,C_106),C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_105))
      | ~ m1_subset_1(k3_subset_1(A_105,C_106),k1_zfmisc_1(A_105)) ) ),
    inference(resolution,[status(thm)],[c_412,c_499])).

tff(c_528,plain,(
    ! [A_109,B_110] :
      ( r1_xboole_0(k3_subset_1(A_109,B_110),B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(resolution,[status(thm)],[c_8,c_514])).

tff(c_531,plain,(
    ! [B_110,A_109] :
      ( r1_xboole_0(B_110,k3_subset_1(A_109,B_110))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(resolution,[status(thm)],[c_528,c_2])).

tff(c_420,plain,(
    ! [A_92,B_93] :
      ( k4_subset_1(A_92,B_93,k3_subset_1(A_92,B_93)) = A_92
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_431,plain,(
    k4_subset_1(k2_struct_0('#skF_1'),'#skF_2',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_65,c_420])).

tff(c_432,plain,(
    ! [A_4] : k4_subset_1(A_4,A_4,k3_subset_1(A_4,A_4)) = A_4 ),
    inference(resolution,[status(thm)],[c_41,c_420])).

tff(c_562,plain,(
    ! [A_123,B_124,C_125] :
      ( k7_subset_1(u1_struct_0(A_123),k2_struct_0(A_123),B_124) = C_125
      | ~ r1_xboole_0(B_124,C_125)
      | k4_subset_1(u1_struct_0(A_123),B_124,C_125) != k2_struct_0(A_123)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_571,plain,(
    ! [A_123] :
      ( k7_subset_1(u1_struct_0(A_123),k2_struct_0(A_123),u1_struct_0(A_123)) = k3_subset_1(u1_struct_0(A_123),u1_struct_0(A_123))
      | ~ r1_xboole_0(u1_struct_0(A_123),k3_subset_1(u1_struct_0(A_123),u1_struct_0(A_123)))
      | u1_struct_0(A_123) != k2_struct_0(A_123)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_123),u1_struct_0(A_123)),k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(u1_struct_0(A_123),k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_struct_0(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_562])).

tff(c_577,plain,(
    ! [A_126] :
      ( k7_subset_1(u1_struct_0(A_126),k2_struct_0(A_126),u1_struct_0(A_126)) = k3_subset_1(u1_struct_0(A_126),u1_struct_0(A_126))
      | ~ r1_xboole_0(u1_struct_0(A_126),k3_subset_1(u1_struct_0(A_126),u1_struct_0(A_126)))
      | u1_struct_0(A_126) != k2_struct_0(A_126)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_126),u1_struct_0(A_126)),k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_struct_0(A_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_571])).

tff(c_580,plain,(
    ! [A_126] :
      ( k7_subset_1(u1_struct_0(A_126),k2_struct_0(A_126),u1_struct_0(A_126)) = k3_subset_1(u1_struct_0(A_126),u1_struct_0(A_126))
      | ~ r1_xboole_0(u1_struct_0(A_126),k3_subset_1(u1_struct_0(A_126),u1_struct_0(A_126)))
      | u1_struct_0(A_126) != k2_struct_0(A_126)
      | ~ l1_struct_0(A_126)
      | ~ m1_subset_1(u1_struct_0(A_126),k1_zfmisc_1(u1_struct_0(A_126))) ) ),
    inference(resolution,[status(thm)],[c_8,c_577])).

tff(c_603,plain,(
    ! [A_127] :
      ( k7_subset_1(u1_struct_0(A_127),k2_struct_0(A_127),u1_struct_0(A_127)) = k3_subset_1(u1_struct_0(A_127),u1_struct_0(A_127))
      | ~ r1_xboole_0(u1_struct_0(A_127),k3_subset_1(u1_struct_0(A_127),u1_struct_0(A_127)))
      | u1_struct_0(A_127) != k2_struct_0(A_127)
      | ~ l1_struct_0(A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_580])).

tff(c_606,plain,(
    ! [A_127] :
      ( k7_subset_1(u1_struct_0(A_127),k2_struct_0(A_127),u1_struct_0(A_127)) = k3_subset_1(u1_struct_0(A_127),u1_struct_0(A_127))
      | u1_struct_0(A_127) != k2_struct_0(A_127)
      | ~ l1_struct_0(A_127)
      | ~ m1_subset_1(u1_struct_0(A_127),k1_zfmisc_1(u1_struct_0(A_127))) ) ),
    inference(resolution,[status(thm)],[c_531,c_603])).

tff(c_625,plain,(
    ! [A_128] :
      ( k7_subset_1(u1_struct_0(A_128),k2_struct_0(A_128),u1_struct_0(A_128)) = k3_subset_1(u1_struct_0(A_128),u1_struct_0(A_128))
      | u1_struct_0(A_128) != k2_struct_0(A_128)
      | ~ l1_struct_0(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_606])).

tff(c_640,plain,
    ( k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),u1_struct_0('#skF_1')) = k3_subset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
    | u1_struct_0('#skF_1') != k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_625])).

tff(c_651,plain,
    ( k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_64,c_64,c_640])).

tff(c_654,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_651])).

tff(c_658,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_654])).

tff(c_662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_658])).

tff(c_664,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_651])).

tff(c_573,plain,(
    ! [B_124,C_125] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_124) = C_125
      | ~ r1_xboole_0(B_124,C_125)
      | k4_subset_1(k2_struct_0('#skF_1'),B_124,C_125) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_562])).

tff(c_576,plain,(
    ! [B_124,C_125] :
      ( k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_124) = C_125
      | ~ r1_xboole_0(B_124,C_125)
      | k4_subset_1(k2_struct_0('#skF_1'),B_124,C_125) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_64,c_573])).

tff(c_735,plain,(
    ! [B_133,C_134] :
      ( k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_133) = C_134
      | ~ r1_xboole_0(B_133,C_134)
      | k4_subset_1(k2_struct_0('#skF_1'),B_133,C_134) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_664,c_576])).

tff(c_743,plain,
    ( k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')
    | ~ r1_xboole_0('#skF_2',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_735])).

tff(c_751,plain,
    ( k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')
    | ~ r1_xboole_0('#skF_2',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_743])).

tff(c_755,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_751])).

tff(c_778,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_755])).

tff(c_785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_778])).

tff(c_786,plain,
    ( ~ r1_xboole_0('#skF_2',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_751])).

tff(c_797,plain,(
    ~ r1_xboole_0('#skF_2',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_786])).

tff(c_800,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_531,c_797])).

tff(c_804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_800])).

tff(c_805,plain,(
    k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_786])).

tff(c_522,plain,(
    ! [A_107,B_108] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_107),k2_struct_0(A_107),B_108),A_107)
      | ~ v4_pre_topc(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_525,plain,(
    ! [B_108] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_108),'#skF_1')
      | ~ v4_pre_topc(B_108,'#skF_1')
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_522])).

tff(c_527,plain,(
    ! [B_108] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_108),'#skF_1')
      | ~ v4_pre_topc(B_108,'#skF_1')
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_64,c_525])).

tff(c_820,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_805,c_527])).

tff(c_826,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_397,c_820])).

tff(c_828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_396,c_826])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.47  
% 3.11/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.47  %$ v4_pre_topc > v3_pre_topc > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_subset_1 > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.11/1.47  
% 3.11/1.47  %Foreground sorts:
% 3.11/1.47  
% 3.11/1.47  
% 3.11/1.47  %Background operators:
% 3.11/1.47  
% 3.11/1.47  
% 3.11/1.47  %Foreground operators:
% 3.11/1.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.11/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.47  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.11/1.47  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.11/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.11/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.47  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.11/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.11/1.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.11/1.47  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.11/1.47  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.11/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.47  
% 3.26/1.49  tff(f_95, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 3.26/1.49  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.26/1.49  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.26/1.49  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.26/1.49  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.26/1.49  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.26/1.49  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.26/1.49  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 3.26/1.49  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.26/1.49  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 3.26/1.49  tff(f_85, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((k2_struct_0(A) = k4_subset_1(u1_struct_0(A), B, C)) & r1_xboole_0(B, C)) => (C = k7_subset_1(u1_struct_0(A), k2_struct_0(A), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_pre_topc)).
% 3.26/1.49  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_pre_topc)).
% 3.26/1.49  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.26/1.49  tff(c_26, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.26/1.49  tff(c_55, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.26/1.49  tff(c_60, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_26, c_55])).
% 3.26/1.49  tff(c_64, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_60])).
% 3.26/1.49  tff(c_34, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.26/1.49  tff(c_70, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_34])).
% 3.26/1.49  tff(c_71, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_70])).
% 3.26/1.49  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.26/1.49  tff(c_65, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_30])).
% 3.26/1.49  tff(c_40, plain, (v4_pre_topc('#skF_2', '#skF_1') | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.26/1.49  tff(c_87, plain, (v4_pre_topc('#skF_2', '#skF_1') | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_40])).
% 3.26/1.49  tff(c_88, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_71, c_87])).
% 3.26/1.49  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.26/1.49  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.49  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.49  tff(c_41, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 3.26/1.49  tff(c_72, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.26/1.49  tff(c_80, plain, (![A_4]: (r1_tarski(A_4, A_4))), inference(resolution, [status(thm)], [c_41, c_72])).
% 3.26/1.49  tff(c_95, plain, (![B_44, C_45, A_46]: (r1_xboole_0(B_44, C_45) | ~r1_tarski(B_44, k3_subset_1(A_46, C_45)) | ~m1_subset_1(C_45, k1_zfmisc_1(A_46)) | ~m1_subset_1(B_44, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.26/1.49  tff(c_189, plain, (![A_57, C_58]: (r1_xboole_0(k3_subset_1(A_57, C_58), C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(A_57)) | ~m1_subset_1(k3_subset_1(A_57, C_58), k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_80, c_95])).
% 3.26/1.49  tff(c_197, plain, (![A_59, B_60]: (r1_xboole_0(k3_subset_1(A_59, B_60), B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(resolution, [status(thm)], [c_8, c_189])).
% 3.26/1.49  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.49  tff(c_200, plain, (![B_60, A_59]: (r1_xboole_0(B_60, k3_subset_1(A_59, B_60)) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(resolution, [status(thm)], [c_197, c_2])).
% 3.26/1.49  tff(c_10, plain, (![A_7, B_8]: (k4_subset_1(A_7, B_8, k3_subset_1(A_7, B_8))=k2_subset_1(A_7) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.26/1.49  tff(c_106, plain, (![A_47, B_48]: (k4_subset_1(A_47, B_48, k3_subset_1(A_47, B_48))=A_47 | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 3.26/1.49  tff(c_117, plain, (k4_subset_1(k2_struct_0('#skF_1'), '#skF_2', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_65, c_106])).
% 3.26/1.49  tff(c_232, plain, (![A_72, B_73, C_74]: (k7_subset_1(u1_struct_0(A_72), k2_struct_0(A_72), B_73)=C_74 | ~r1_xboole_0(B_73, C_74) | k4_subset_1(u1_struct_0(A_72), B_73, C_74)!=k2_struct_0(A_72) | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0(A_72))) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.26/1.49  tff(c_243, plain, (![B_73, C_74]: (k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_73)=C_74 | ~r1_xboole_0(B_73, C_74) | k4_subset_1(k2_struct_0('#skF_1'), B_73, C_74)!=k2_struct_0('#skF_1') | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_232])).
% 3.26/1.49  tff(c_246, plain, (![B_73, C_74]: (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_73)=C_74 | ~r1_xboole_0(B_73, C_74) | k4_subset_1(k2_struct_0('#skF_1'), B_73, C_74)!=k2_struct_0('#skF_1') | ~m1_subset_1(C_74, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_64, c_243])).
% 3.26/1.49  tff(c_252, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_246])).
% 3.26/1.49  tff(c_255, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_252])).
% 3.26/1.49  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_255])).
% 3.26/1.49  tff(c_267, plain, (![B_78, C_79]: (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_78)=C_79 | ~r1_xboole_0(B_78, C_79) | k4_subset_1(k2_struct_0('#skF_1'), B_78, C_79)!=k2_struct_0('#skF_1') | ~m1_subset_1(C_79, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_78, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_246])).
% 3.26/1.49  tff(c_272, plain, (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2') | ~r1_xboole_0('#skF_2', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_117, c_267])).
% 3.26/1.49  tff(c_282, plain, (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2') | ~r1_xboole_0('#skF_2', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_272])).
% 3.26/1.49  tff(c_287, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_282])).
% 3.26/1.49  tff(c_290, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_287])).
% 3.26/1.49  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_290])).
% 3.26/1.49  tff(c_298, plain, (~r1_xboole_0('#skF_2', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_282])).
% 3.26/1.49  tff(c_333, plain, (~r1_xboole_0('#skF_2', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_298])).
% 3.26/1.49  tff(c_336, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_200, c_333])).
% 3.26/1.49  tff(c_340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_336])).
% 3.26/1.49  tff(c_341, plain, (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_298])).
% 3.26/1.49  tff(c_212, plain, (![B_66, A_67]: (v4_pre_topc(B_66, A_67) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_67), k2_struct_0(A_67), B_66), A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.26/1.49  tff(c_218, plain, (![B_66]: (v4_pre_topc(B_66, '#skF_1') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_66), '#skF_1') | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_212])).
% 3.26/1.49  tff(c_221, plain, (![B_66]: (v4_pre_topc(B_66, '#skF_1') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_66), '#skF_1') | ~m1_subset_1(B_66, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_64, c_218])).
% 3.26/1.49  tff(c_386, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_341, c_221])).
% 3.26/1.49  tff(c_393, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_88, c_386])).
% 3.26/1.49  tff(c_395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_393])).
% 3.26/1.49  tff(c_396, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_70])).
% 3.26/1.49  tff(c_397, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_70])).
% 3.26/1.49  tff(c_400, plain, (![A_85, B_86]: (r1_tarski(A_85, B_86) | ~m1_subset_1(A_85, k1_zfmisc_1(B_86)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.26/1.49  tff(c_412, plain, (![A_4]: (r1_tarski(A_4, A_4))), inference(resolution, [status(thm)], [c_41, c_400])).
% 3.26/1.49  tff(c_499, plain, (![B_102, C_103, A_104]: (r1_xboole_0(B_102, C_103) | ~r1_tarski(B_102, k3_subset_1(A_104, C_103)) | ~m1_subset_1(C_103, k1_zfmisc_1(A_104)) | ~m1_subset_1(B_102, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.26/1.49  tff(c_514, plain, (![A_105, C_106]: (r1_xboole_0(k3_subset_1(A_105, C_106), C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(A_105)) | ~m1_subset_1(k3_subset_1(A_105, C_106), k1_zfmisc_1(A_105)))), inference(resolution, [status(thm)], [c_412, c_499])).
% 3.26/1.49  tff(c_528, plain, (![A_109, B_110]: (r1_xboole_0(k3_subset_1(A_109, B_110), B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(resolution, [status(thm)], [c_8, c_514])).
% 3.26/1.49  tff(c_531, plain, (![B_110, A_109]: (r1_xboole_0(B_110, k3_subset_1(A_109, B_110)) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(resolution, [status(thm)], [c_528, c_2])).
% 3.26/1.49  tff(c_420, plain, (![A_92, B_93]: (k4_subset_1(A_92, B_93, k3_subset_1(A_92, B_93))=A_92 | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 3.26/1.49  tff(c_431, plain, (k4_subset_1(k2_struct_0('#skF_1'), '#skF_2', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_65, c_420])).
% 3.26/1.49  tff(c_432, plain, (![A_4]: (k4_subset_1(A_4, A_4, k3_subset_1(A_4, A_4))=A_4)), inference(resolution, [status(thm)], [c_41, c_420])).
% 3.26/1.49  tff(c_562, plain, (![A_123, B_124, C_125]: (k7_subset_1(u1_struct_0(A_123), k2_struct_0(A_123), B_124)=C_125 | ~r1_xboole_0(B_124, C_125) | k4_subset_1(u1_struct_0(A_123), B_124, C_125)!=k2_struct_0(A_123) | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_123))) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.26/1.49  tff(c_571, plain, (![A_123]: (k7_subset_1(u1_struct_0(A_123), k2_struct_0(A_123), u1_struct_0(A_123))=k3_subset_1(u1_struct_0(A_123), u1_struct_0(A_123)) | ~r1_xboole_0(u1_struct_0(A_123), k3_subset_1(u1_struct_0(A_123), u1_struct_0(A_123))) | u1_struct_0(A_123)!=k2_struct_0(A_123) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_123), u1_struct_0(A_123)), k1_zfmisc_1(u1_struct_0(A_123))) | ~m1_subset_1(u1_struct_0(A_123), k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_struct_0(A_123))), inference(superposition, [status(thm), theory('equality')], [c_432, c_562])).
% 3.26/1.49  tff(c_577, plain, (![A_126]: (k7_subset_1(u1_struct_0(A_126), k2_struct_0(A_126), u1_struct_0(A_126))=k3_subset_1(u1_struct_0(A_126), u1_struct_0(A_126)) | ~r1_xboole_0(u1_struct_0(A_126), k3_subset_1(u1_struct_0(A_126), u1_struct_0(A_126))) | u1_struct_0(A_126)!=k2_struct_0(A_126) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_126), u1_struct_0(A_126)), k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_struct_0(A_126))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_571])).
% 3.26/1.49  tff(c_580, plain, (![A_126]: (k7_subset_1(u1_struct_0(A_126), k2_struct_0(A_126), u1_struct_0(A_126))=k3_subset_1(u1_struct_0(A_126), u1_struct_0(A_126)) | ~r1_xboole_0(u1_struct_0(A_126), k3_subset_1(u1_struct_0(A_126), u1_struct_0(A_126))) | u1_struct_0(A_126)!=k2_struct_0(A_126) | ~l1_struct_0(A_126) | ~m1_subset_1(u1_struct_0(A_126), k1_zfmisc_1(u1_struct_0(A_126))))), inference(resolution, [status(thm)], [c_8, c_577])).
% 3.26/1.49  tff(c_603, plain, (![A_127]: (k7_subset_1(u1_struct_0(A_127), k2_struct_0(A_127), u1_struct_0(A_127))=k3_subset_1(u1_struct_0(A_127), u1_struct_0(A_127)) | ~r1_xboole_0(u1_struct_0(A_127), k3_subset_1(u1_struct_0(A_127), u1_struct_0(A_127))) | u1_struct_0(A_127)!=k2_struct_0(A_127) | ~l1_struct_0(A_127))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_580])).
% 3.26/1.49  tff(c_606, plain, (![A_127]: (k7_subset_1(u1_struct_0(A_127), k2_struct_0(A_127), u1_struct_0(A_127))=k3_subset_1(u1_struct_0(A_127), u1_struct_0(A_127)) | u1_struct_0(A_127)!=k2_struct_0(A_127) | ~l1_struct_0(A_127) | ~m1_subset_1(u1_struct_0(A_127), k1_zfmisc_1(u1_struct_0(A_127))))), inference(resolution, [status(thm)], [c_531, c_603])).
% 3.26/1.49  tff(c_625, plain, (![A_128]: (k7_subset_1(u1_struct_0(A_128), k2_struct_0(A_128), u1_struct_0(A_128))=k3_subset_1(u1_struct_0(A_128), u1_struct_0(A_128)) | u1_struct_0(A_128)!=k2_struct_0(A_128) | ~l1_struct_0(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_606])).
% 3.26/1.49  tff(c_640, plain, (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), u1_struct_0('#skF_1'))=k3_subset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1')) | u1_struct_0('#skF_1')!=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_64, c_625])).
% 3.26/1.49  tff(c_651, plain, (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_64, c_64, c_640])).
% 3.26/1.49  tff(c_654, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_651])).
% 3.26/1.49  tff(c_658, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_654])).
% 3.26/1.49  tff(c_662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_658])).
% 3.26/1.49  tff(c_664, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_651])).
% 3.26/1.49  tff(c_573, plain, (![B_124, C_125]: (k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_124)=C_125 | ~r1_xboole_0(B_124, C_125) | k4_subset_1(k2_struct_0('#skF_1'), B_124, C_125)!=k2_struct_0('#skF_1') | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_562])).
% 3.26/1.49  tff(c_576, plain, (![B_124, C_125]: (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_124)=C_125 | ~r1_xboole_0(B_124, C_125) | k4_subset_1(k2_struct_0('#skF_1'), B_124, C_125)!=k2_struct_0('#skF_1') | ~m1_subset_1(C_125, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_124, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_64, c_573])).
% 3.26/1.49  tff(c_735, plain, (![B_133, C_134]: (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_133)=C_134 | ~r1_xboole_0(B_133, C_134) | k4_subset_1(k2_struct_0('#skF_1'), B_133, C_134)!=k2_struct_0('#skF_1') | ~m1_subset_1(C_134, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_133, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_664, c_576])).
% 3.26/1.49  tff(c_743, plain, (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2') | ~r1_xboole_0('#skF_2', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_431, c_735])).
% 3.26/1.49  tff(c_751, plain, (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2') | ~r1_xboole_0('#skF_2', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_743])).
% 3.26/1.49  tff(c_755, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_751])).
% 3.26/1.49  tff(c_778, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_755])).
% 3.26/1.49  tff(c_785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_778])).
% 3.26/1.49  tff(c_786, plain, (~r1_xboole_0('#skF_2', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_751])).
% 3.26/1.49  tff(c_797, plain, (~r1_xboole_0('#skF_2', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_786])).
% 3.26/1.49  tff(c_800, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_531, c_797])).
% 3.26/1.49  tff(c_804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_800])).
% 3.26/1.49  tff(c_805, plain, (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_786])).
% 3.26/1.49  tff(c_522, plain, (![A_107, B_108]: (v3_pre_topc(k7_subset_1(u1_struct_0(A_107), k2_struct_0(A_107), B_108), A_107) | ~v4_pre_topc(B_108, A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.26/1.49  tff(c_525, plain, (![B_108]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_108), '#skF_1') | ~v4_pre_topc(B_108, '#skF_1') | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_522])).
% 3.26/1.49  tff(c_527, plain, (![B_108]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_108), '#skF_1') | ~v4_pre_topc(B_108, '#skF_1') | ~m1_subset_1(B_108, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_64, c_525])).
% 3.26/1.49  tff(c_820, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_805, c_527])).
% 3.26/1.49  tff(c_826, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_397, c_820])).
% 3.26/1.49  tff(c_828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_396, c_826])).
% 3.26/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.49  
% 3.26/1.49  Inference rules
% 3.26/1.49  ----------------------
% 3.26/1.49  #Ref     : 0
% 3.26/1.49  #Sup     : 160
% 3.26/1.49  #Fact    : 0
% 3.26/1.49  #Define  : 0
% 3.26/1.49  #Split   : 10
% 3.26/1.49  #Chain   : 0
% 3.26/1.49  #Close   : 0
% 3.26/1.49  
% 3.26/1.49  Ordering : KBO
% 3.26/1.49  
% 3.26/1.49  Simplification rules
% 3.26/1.49  ----------------------
% 3.26/1.49  #Subsume      : 13
% 3.26/1.49  #Demod        : 242
% 3.26/1.49  #Tautology    : 61
% 3.26/1.49  #SimpNegUnit  : 8
% 3.26/1.49  #BackRed      : 1
% 3.26/1.49  
% 3.26/1.49  #Partial instantiations: 0
% 3.26/1.49  #Strategies tried      : 1
% 3.26/1.49  
% 3.26/1.49  Timing (in seconds)
% 3.26/1.49  ----------------------
% 3.26/1.50  Preprocessing        : 0.32
% 3.26/1.50  Parsing              : 0.18
% 3.26/1.50  CNF conversion       : 0.02
% 3.26/1.50  Main loop            : 0.40
% 3.26/1.50  Inferencing          : 0.14
% 3.26/1.50  Reduction            : 0.13
% 3.26/1.50  Demodulation         : 0.10
% 3.26/1.50  BG Simplification    : 0.02
% 3.26/1.50  Subsumption          : 0.07
% 3.26/1.50  Abstraction          : 0.02
% 3.26/1.50  MUC search           : 0.00
% 3.26/1.50  Cooper               : 0.00
% 3.26/1.50  Total                : 0.77
% 3.26/1.50  Index Insertion      : 0.00
% 3.26/1.50  Index Deletion       : 0.00
% 3.26/1.50  Index Matching       : 0.00
% 3.26/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
