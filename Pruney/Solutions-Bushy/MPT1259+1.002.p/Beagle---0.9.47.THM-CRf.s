%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1259+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:39 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 187 expanded)
%              Number of leaves         :   25 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          :   96 ( 417 expanded)
%              Number of equality atoms :   31 ( 112 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => k2_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k2_tops_1(A,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,k2_tops_1(A,B)) = k2_tops_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l79_tops_1)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_71,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l80_tops_1)).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k2_tops_1(A_1,B_2),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_56,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k2_tops_1(A_32,B_33),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14] :
      ( k7_subset_1(A_12,B_13,C_14) = k4_xboole_0(B_13,C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_105,plain,(
    ! [A_40,B_41,C_42] :
      ( k7_subset_1(u1_struct_0(A_40),k2_tops_1(A_40,B_41),C_42) = k4_xboole_0(k2_tops_1(A_40,B_41),C_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_56,c_10])).

tff(c_109,plain,(
    ! [C_42] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),C_42) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),C_42)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_105])).

tff(c_113,plain,(
    ! [C_42] : k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),C_42) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),C_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_109])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_73,plain,(
    ! [A_36,B_37] :
      ( k2_pre_topc(A_36,k2_tops_1(A_36,B_37)) = k2_tops_1(A_36,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_77,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_81,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_77])).

tff(c_86,plain,(
    ! [A_38,B_39] :
      ( k7_subset_1(u1_struct_0(A_38),k2_pre_topc(A_38,B_39),k1_tops_1(A_38,B_39)) = k2_tops_1(A_38,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_86])).

tff(c_102,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_95])).

tff(c_135,plain,
    ( k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_102])).

tff(c_136,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_139,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_136])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_139])).

tff(c_145,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_20,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) != k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_59,plain,(
    ! [A_32,B_33,C_14] :
      ( k7_subset_1(u1_struct_0(A_32),k2_tops_1(A_32,B_33),C_14) = k4_xboole_0(k2_tops_1(A_32,B_33),C_14)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_56,c_10])).

tff(c_147,plain,(
    ! [C_14] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_14) = k4_xboole_0(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_14)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_145,c_59])).

tff(c_156,plain,(
    ! [C_14] : k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_14) = k4_xboole_0(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_147])).

tff(c_6,plain,(
    ! [A_6,B_8] :
      ( k2_pre_topc(A_6,k2_tops_1(A_6,B_8)) = k2_tops_1(A_6,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_149,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_145,c_6])).

tff(c_159,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_149])).

tff(c_60,plain,(
    ! [A_34,B_35] :
      ( k1_tops_1(A_34,k2_tops_1(A_34,k2_tops_1(A_34,B_35))) = k1_xboole_0
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_64,plain,
    ( k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_60])).

tff(c_68,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_64])).

tff(c_98,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_86])).

tff(c_104,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_98])).

tff(c_253,plain,
    ( k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_156,c_159,c_104])).

tff(c_254,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_253])).

tff(c_257,plain,
    ( ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_254])).

tff(c_261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_145,c_257])).

%------------------------------------------------------------------------------
