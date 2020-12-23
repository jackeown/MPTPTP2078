%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1277+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:42 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 160 expanded)
%              Number of leaves         :   27 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  107 ( 376 expanded)
%              Number of equality atoms :   22 (  55 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_tops_1(k2_tops_1(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tops_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_tops_1(k2_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc16_tops_1)).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_13),B_14),A_13)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ v4_pre_topc(B_14,A_13)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    ~ v3_tops_1(k2_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k3_subset_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_86,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k2_pre_topc(A_33,B_34),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_17,B_18,C_19] :
      ( k9_subset_1(A_17,B_18,C_19) = k3_xboole_0(B_18,C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_250,plain,(
    ! [A_51,B_52,B_53] :
      ( k9_subset_1(u1_struct_0(A_51),B_52,k2_pre_topc(A_51,B_53)) = k3_xboole_0(B_52,k2_pre_topc(A_51,B_53))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_86,c_16])).

tff(c_257,plain,(
    ! [B_52] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_52,k2_pre_topc('#skF_1','#skF_2')) = k3_xboole_0(B_52,k2_pre_topc('#skF_1','#skF_2'))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_250])).

tff(c_262,plain,(
    ! [B_52] : k9_subset_1(u1_struct_0('#skF_1'),B_52,k2_pre_topc('#skF_1','#skF_2')) = k3_xboole_0(B_52,k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_257])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( k9_subset_1(A_1,C_3,B_2) = k9_subset_1(A_1,B_2,C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_492,plain,(
    ! [A_65,B_66,B_67] :
      ( k9_subset_1(u1_struct_0(A_65),k2_pre_topc(A_65,B_66),B_67) = k9_subset_1(u1_struct_0(A_65),B_67,k2_pre_topc(A_65,B_66))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_86,c_2])).

tff(c_499,plain,(
    ! [B_67] :
      ( k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),B_67) = k9_subset_1(u1_struct_0('#skF_1'),B_67,k2_pre_topc('#skF_1','#skF_2'))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_492])).

tff(c_505,plain,(
    ! [B_68] : k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),B_68) = k3_xboole_0(B_68,k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_262,c_499])).

tff(c_4,plain,(
    ! [A_4,B_6] :
      ( k9_subset_1(u1_struct_0(A_4),k2_pre_topc(A_4,B_6),k2_pre_topc(A_4,k3_subset_1(u1_struct_0(A_4),B_6))) = k2_tops_1(A_4,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_520,plain,
    ( k3_xboole_0(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k2_pre_topc('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_4])).

tff(c_555,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k2_pre_topc('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_520])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( k3_subset_1(A_23,k3_subset_1(A_23,B_24)) = B_24
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_28])).

tff(c_232,plain,(
    ! [A_49,B_50] :
      ( k9_subset_1(u1_struct_0(A_49),k2_pre_topc(A_49,B_50),k2_pre_topc(A_49,k3_subset_1(u1_struct_0(A_49),B_50))) = k2_tops_1(A_49,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_245,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k2_pre_topc('#skF_1','#skF_2')) = k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_232])).

tff(c_249,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k2_pre_topc('#skF_1','#skF_2')) = k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_245])).

tff(c_1240,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_262,c_249])).

tff(c_1241,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1240])).

tff(c_1244,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_1241])).

tff(c_1248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1244])).

tff(c_1249,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1240])).

tff(c_144,plain,(
    ! [A_40,B_41] :
      ( v3_tops_1(k2_tops_1(A_40,B_41),A_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ v3_pre_topc(B_41,A_40)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_153,plain,(
    ! [A_40,B_10] :
      ( v3_tops_1(k2_tops_1(A_40,k3_subset_1(u1_struct_0(A_40),B_10)),A_40)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_40),B_10),A_40)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_40))) ) ),
    inference(resolution,[status(thm)],[c_8,c_144])).

tff(c_1293,plain,
    ( v3_tops_1(k2_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1249,c_153])).

tff(c_1297,plain,
    ( v3_tops_1(k2_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_24,c_1293])).

tff(c_1298,plain,(
    ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_1297])).

tff(c_1302,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_1298])).

tff(c_1306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_22,c_1302])).

%------------------------------------------------------------------------------
